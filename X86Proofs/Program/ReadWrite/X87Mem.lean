import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Program.ReadWrite.Rmw

/-!
# x87 forms with a memory operand

The x87 memory forms (`FLD m32fp`, `FILD m16int`, `FADD m64fp`, `FCOM m32fp`, `FST m32fp`, `FIST
m16int`, `FLDCW m16`, …) are register-stack forms with a memory access: a load (`Logical_Mem_Read`,
which uses up oracle bits and records a trace event, `dataAccess t "load"`), the address check of
a store (`Check_Logical_Address_Is_Writable`, oracle bits only), a store (`Logical_Mem_Write`:
`dataAccess t "store"` and the bytes written). Their preconditions add the operand's bytes to
`X87Pre`: `X87LoadPre p top addr len` (readable) and `X87StorePre p top codeLen addr len`
(writable and apart from the instruction's code); with an FS/GS override `r` the address is
`base + addr` and `r.Ready base` is a further conjunct, as for the other memory families.

- Loads end in `x87Out (g t) …` where `g` only uses up oracle bits and records trace events
  (`OnlyTrace g`: `dataAccess t "load"`, and for `FLD m80fp` two loads after an address check). The
  effect is the register-stack form's `x87Effect` (`x87Effect_holds_trace`): what the oracle and
  the trace hold is not part of any effect (`Effect.Holds.oracle_trace`).
- Stores end in `x87Out (g t) …` where `g` also stores `v t` at `a` (`StoreTrace g a v`: the
  address check, the store's `dataAccess t "store"` and its bytes). The effect is
  `x87StoreEffect`, the memory write and `x87Effect`'s (`x87StoreEffect_holds`), and the state
  after it is ready to step again if the bytes lie below 4 GiB and off the page tables
  (`ReadyToStep.of_x87Store`).
- The control forms FLDCW, FNSTCW and FNSTSW with a memory operand keep the register stack and
  FIP: FLDCW leaves `x87LdcwOut` (the control word loaded, the condition codes from the oracle)
  after its load, FNSTCW and FNSTSW store a word after `x87CtlOut` (the condition codes from the
  oracle). Their effects list the control word or the stored word and `.fcc` (all four codes
  undefined): `x87LdcwEffect_holds`, `x87CtlStoreEffect_holds`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The precondition of an x87 triple at `p` with stack top `top` that reads the `len` bytes at
`addr s`: `X87Pre`, and the bytes readable. -/
structure X87LoadPre [Bindings] (p : BitVec 64) (top : BitVec 3) (addr : RamState → BitVec 64)
    (len : Nat) (s : RamState) : Prop extends X87Pre p top s where
  read : MemReadable s (addr s) len

/-- The precondition of an x87 triple at `p` (an instruction of `codeLen` bytes) with stack top
`top` that writes the `len` bytes at `addr s`: `X87Pre`, the bytes writable and apart from the
instruction's code (`StorePre`). -/
structure X87StorePre [Bindings] (p : BitVec 64) (top : BitVec 3) (codeLen : Nat)
    (addr : RamState → BitVec 64) (len : Nat) (s : RamState) : Prop extends X87Pre p top s where
  write : MemWritable s (addr s) len
  code : RangeApart (addr s) len p codeLen

theorem X87StorePre.storePre [Bindings] {p : BitVec 64} {top : BitVec 3} {codeLen : Nat}
    {addr : RamState → BitVec 64} {len : Nat} {s : RamState}
    (h : X87StorePre p top codeLen addr len s) : StorePre p codeLen addr len s :=
  ⟨h.rip, h.write, h.code⟩

/-! ### Oracle and trace -/

@[simp] theorem dataAccess_FP87 (s : RamState) (event : String) :
    (dataAccess s event).FP87 = s.FP87 := rfl

@[simp] theorem dataAccess_FP87_Control (s : RamState) (event : String) :
    (dataAccess s event).FP87_Control = s.FP87_Control := rfl

@[simp] theorem dataAccess_FP87_Tag_Word (s : RamState) (event : String) :
    (dataAccess s event).FP87_Tag_Word = s.FP87_Tag_Word := rfl

/-- `g` changes at most the oracle and the trace of memory accesses. -/
def OnlyTrace (g : RamState → RamState) : Prop :=
  ∀ t, g t = { t with oracle := (g t).oracle, traceEventsRev := (g t).traceEventsRev }

theorem OnlyTrace.dataAccess (ev : String) : OnlyTrace fun t => dataAccess t ev := fun _ => rfl

theorem Operand.read_oracle_trace {n : Nat} (s : RamState) (o : X86.Runtime.Oracle)
    (tr : List (String × String)) (op : Operand n) :
    op.read { s with oracle := o, traceEventsRev := tr } = op.read s :=
  Operand.read_of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl op

/-- An effect does not constrain the oracle or the trace of memory accesses. -/
theorem Effect.Holds.oracle_trace {e : Effect} {s s' : RamState} (h : e.Holds s s')
    (o : X86.Runtime.Oracle) (tr : List (String × String)) :
    e.Holds s { s' with oracle := o, traceEventsRev := tr } := by
  refine ⟨h.rip, ?_, h.flags, ?_⟩
  · rw [Write.allHold_iff]
    intro w hw
    rw [Operand.read_oracle_trace]
    exact Write.allHold_iff.mp h.writes w hw
  · refine ⟨fun c hc hm => ?_, h.agrees.memory, ?_, h.agrees.grow⟩
    · have := h.agrees.agree c hc hm
      cases c <;> exact this
    · rw [← h.agrees.rest]
      rfl

/-- `x87Effect_holds` for a form whose memory accesses only use up oracle bits and record trace
events (`g`): the loads. -/
theorem x87Effect_holds_trace [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (p : BitVec 64) (hp : s.RIP = p) (g : RamState → RamState) (hg : OnlyTrace g)
    (k : RamState → Nat) (regs : List (BitVec 3 × BitVec 80))
    (fp : RamState → X86.Runtime.Array 8 F80_Type) (ftw fsw : RamState → BitVec 16)
    (ftwV fswV : BitVec 16) (m cc : BitVec 4)
    (hregs : ∀ rv ∈ regs, (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex rv.1] = rv.2)
    (hfp : ∀ r : BitVec 3, r ∉ regs.map Prod.fst →
      (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex r] = s.FP87[fprIndex r])
    (hftw : ftw (afterFetches (beforeFetch s) (length + 1)) = ftwV)
    (hfsw : fswRest (fsw (afterFetches (beforeFetch s) (length + 1))) = fswV)
    (hcc : fswCC (fsw (afterFetches (beforeFetch s) (length + 1))) &&& m = cc) :
    (x87Effect p length regs ftwV fswV m cc s).Holds s
      (afterStep s length fun t =>
        x87Out (g t) (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t)) := by
  have H := x87Effect_holds h length p hp k regs fp ftw fsw ftwV fswV m cc hregs hfp hftw hfsw hcc
  let t := afterFetches (beforeFetch s) (length + 1)
  have E : (afterStep s length fun t =>
      x87Out (g t) (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t)) =
      { (afterStep s length fun t =>
          x87Out t (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t)) with
        oracle := oracleSkip (g t).oracle (k t), traceEventsRev := (g t).traceEventsRev } := by
    have E1 : x87Out (g t) (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t) =
        { x87Out t (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t) with
          oracle := oracleSkip (g t).oracle (k t), traceEventsRev := (g t).traceEventsRev } := by
      conv => lhs; rw [hg t]
      rfl
    show finishStep (x87Out (g t) _ _ _ _ _) = _
    rw [E1]
    rfl
  rw [E]
  exact H.oracle_trace _ _

/-! ### Stores -/

/-- `g` changes at most the oracle and the trace of memory accesses, and stores the `n` bits
`v t` at `a`. -/
def StoreTrace {n : Nat} (g : RamState → RamState) (a : BitVec 64) (v : RamState → BitVec n) :
    Prop :=
  ∀ t, g t = { t with
    oracle := (g t).oracle
    traceEventsRev := (g t).traceEventsRev
    external := memStore t.external a (v t) }

/-- The effect of an x87 step at `p` of `len` bytes that stores `v` (`n` bits) at `a`: that write,
and those of `x87Effect`. -/
def x87StoreEffect (p : BitVec 64) (len : Nat) {n : Nat} (a : BitVec 64) (v : BitVec n)
    (regs : List (BitVec 3 × BitVec 80)) (ftw fsw : BitVec 16) (m cc : BitVec 4) (s : RamState) :
    Effect :=
  { x87Effect p len regs ftw fsw m cc s with
    writes := ⟨(Operand.mem a : Operand n), v⟩ :: (x87Effect p len regs ftw fsw m cc s).writes }

theorem x87StoreEffect_components (p : BitVec 64) (len : Nat) {n : Nat} (a : BitVec 64)
    (v : BitVec n) (regs : List (BitVec 3 × BitVec 80)) (ftw fsw : BitVec 16) (m cc : BitVec 4)
    (s : RamState) :
    (x87StoreEffect p len a v regs ftw fsw m cc s).components =
      .mem a (n / 8) :: ((regs.map Prod.fst).map Component.fpr ++
        [.ftw, .fsw, .fcc, .fpuPtr, .rip]) := by
  simp [x87StoreEffect, x87Effect, Effect.components, Function.comp_def, Write.component,
    Operand.component]

/-- An x87 store effect misses code apart from the bytes it stores. -/
theorem x87StoreEffect_avoids {p : BitVec 64} {len : Nat} {n : Nat} {a : BitVec 64}
    {v : BitVec n} {regs : List (BitVec 3 × BitVec 80)} {ftw fsw : BitVec 16} {m cc : BitVec 4}
    {s : RamState} {q : BitVec 64} {codeLen : Nat} {bytes : List UInt8}
    (hd : RangeApart a (n / 8) q codeLen) (hl : bytes.length = codeLen) :
    (x87StoreEffect p len a v regs ftw fsw m cc s).Avoids (codeRange q bytes) := by
  refine Effect.avoids_of_mem (fun c hc hm => ?_) hd hl
  rw [x87StoreEffect_components] at hc
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | ⟨r, -, rfl⟩ | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | exact absurd hm (by simp [Component.isMem])

/-- A store of `n` bits at `a` on top of a step that changes only `cs`, the oracle and the trace
changes only `cs` and those bytes. -/
theorem AgreesExcept.store_cons {cs : List Component} {s s' : RamState} (h : AgreesExcept cs s s')
    (a : BitVec 64) {n : Nat} (v : BitVec n) (o : X86.Runtime.Oracle)
    (tr : List (String × String)) :
    AgreesExcept (.mem a (n / 8) :: cs) s
      { s' with oracle := o, traceEventsRev := tr, external := memStore s'.external a v } := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · have := h.agree c (fun hc' => hc (List.mem_cons_of_mem _ hc')) hm
    cases c <;> first | exact this | exact absurd hm (by simp [Component.isMem])
  · show (memStore s'.external a v)[x]? = s.external[x]?
    rw [memStore_getElem?_of_ne]
    · exact h.memory x fun c hc => hx c (List.mem_cons_of_mem _ hc)
    · intro i hi he
      exact hx (.mem a (n / 8)) List.mem_cons_self ⟨i, hi, he.symm⟩
  · rw [← h.rest]
    rfl
  · exact memStore_isSome _ _ _ x (h.grow x hx)

theorem Operand.read_x87Effect_store (s' : RamState) (o : X86.Runtime.Oracle)
    (tr : List (String × String)) (ext : Ram) (p : BitVec 64) (len : Nat)
    (regs : List (BitVec 3 × BitVec 80)) (ftw fsw : BitVec 16) (m cc : BitVec 4) (s : RamState)
    (w : Write) (hw : w ∈ (x87Effect p len regs ftw fsw m cc s).writes) :
    w.dst.read { s' with oracle := o, traceEventsRev := tr, external := ext } = w.dst.read s' := by
  simp only [x87Effect, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff,
    or_false] at hw
  rcases hw with ⟨rv, -, rfl⟩ | rfl | rfl | rfl | rfl <;> rfl

/-- A step whose form ends in `x87Out (g t) …` with `g` a store of `v` at `a` has an
`x87StoreEffect`, given the values the form leaves. -/
theorem x87StoreEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (p : BitVec 64) (hp : s.RIP = p) {n : Nat} (hn : n % 8 = 0) (h128 : n ≤ 128) (a : BitVec 64)
    (v : RamState → BitVec n) (g : RamState → RamState) (hg : StoreTrace g a v)
    (k : RamState → Nat) (regs : List (BitVec 3 × BitVec 80))
    (fp : RamState → X86.Runtime.Array 8 F80_Type) (ftw fsw : RamState → BitVec 16)
    (vV : BitVec n) (ftwV fswV : BitVec 16) (m cc : BitVec 4)
    (hv : v (afterFetches (beforeFetch s) (length + 1)) = vV)
    (hregs : ∀ rv ∈ regs, (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex rv.1] = rv.2)
    (hfp : ∀ r : BitVec 3, r ∉ regs.map Prod.fst →
      (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex r] = s.FP87[fprIndex r])
    (hftw : ftw (afterFetches (beforeFetch s) (length + 1)) = ftwV)
    (hfsw : fswRest (fsw (afterFetches (beforeFetch s) (length + 1))) = fswV)
    (hcc : fswCC (fsw (afterFetches (beforeFetch s) (length + 1))) &&& m = cc) :
    (x87StoreEffect p length a vV regs ftwV fswV m cc s).Holds s
      (afterStep s length fun t =>
        x87Out (g t) (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t)) := by
  have H := x87Effect_holds h length p hp k regs fp ftw fsw ftwV fswV m cc hregs hfp hftw hfsw hcc
  let t := afterFetches (beforeFetch s) (length + 1)
  have E : (afterStep s length fun t =>
      x87Out (g t) (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t)) =
      { (afterStep s length fun t =>
          x87Out t (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t)) with
        oracle := oracleSkip (g t).oracle (k t)
        traceEventsRev := (g t).traceEventsRev
        external := memStore s.external a vV } := by
    have E1 : x87Out (g t) (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t) =
        { x87Out t (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t) with
          oracle := oracleSkip (g t).oracle (k t)
          traceEventsRev := (g t).traceEventsRev
          external := memStore s.external a vV } := by
      conv => lhs; rw [hg t]
      rw [← hv]
      rfl
    show finishStep (x87Out (g t) _ _ _ _ _) = _
    rw [E1]
    rfl
  rw [E]
  refine ⟨H.rip, ?_, trivial, ?_⟩
  · rw [Write.allHold_iff]
    intro w hw
    simp only [x87StoreEffect, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact memLoad_memStore _ _ hn h128 vV
    · rw [Operand.read_x87Effect_store _ _ _ _ _ _ _ _ _ _ _ _ w hw]
      exact Write.allHold_iff.mp H.writes w hw
  · rw [x87StoreEffect_components, ← x87Effect_components p length regs ftwV fswV m cc s]
    have := H.agrees.store_cons a vV (oracleSkip (g t).oracle (k t)) (g t).traceEventsRev
    exact this

/-- The state after a step with a store at `a` of `n` bits below 4 GiB and off the page tables
and an effect `e` is ready to step again. -/
theorem ReadyToStep.of_x87Store [Bindings] {s s' : RamState} {e : Effect} (h : ReadyToStep s)
    (hh : e.Holds s s') {a : BitVec 64} {n : Nat} {v : BitVec n}
    (hext : s'.external = memStore s.external a v) (hlow : a.toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart a.toNat (n / 8)) : ReadyToStep s' :=
  h.of_agreesExcept hh.agrees (hext ▸ IdentityPageTableMemory.memStore h.memory.tables a v hlow
    htables)

/-! ### FLDCW, FNSTCW and FNSTSW with a memory operand -/

/-- What FLDCW leaves from the state `t` after its load: `x87CtlOut` (`Next_IP`, `k` oracle bits
used up, the status word `fsw`) with the control word `fcw`. -/
def x87LdcwOut (t : RamState) (ip : BitVec 64) (k : Nat) (fcw fsw : BitVec 16) : RamState :=
  { x87CtlOut t ip k fsw with FP87_Control := fcw }

/-- FLDCW (after its load) changes only the control word, the condition codes (and RIP). -/
theorem AgreesExcept.afterStep_x87Ldcw (s : RamState) (length : Nat) (ip : BitVec 64) (k : Nat)
    (fcw fsw : RamState → BitVec 16)
    (hrest : fswRest (fsw (afterFetches (beforeFetch s) (length + 1))) = fswRest s.FP87_Status) :
    AgreesExcept [.fcw, .fcc, .rip] s
      (afterStep s length fun t => x87LdcwOut t ip k (fcw t) (fsw t)) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | fsw => exact hrest
    | fcw => exact absurd (by simp) hc
    | fcc => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | _ => rfl
  · simp only [fixedPart, afterStep, finishStep, x87LdcwOut, x87CtlOut, afterFetches, beforeFetch,
      resetStepFields]

/-- The effect of FLDCW at `p` of `len` bytes loading the control word `fcw`: FCW := `fcw`, the
condition codes undefined. -/
def x87LdcwEffect (p : BitVec 64) (len : Nat) (fcw : BitVec 16) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.fcw : Operand 16), fcw⟩, ⟨(Operand.fcc 0 : Operand 4), 0⟩]

@[simp] theorem x87LdcwEffect_components (p : BitVec 64) (len : Nat) (fcw : BitVec 16) :
    (x87LdcwEffect p len fcw).components = [.fcw, .fcc, .rip] := rfl

theorem x87LdcwEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (p : BitVec 64) (hp : s.RIP = p) (g : RamState → RamState) (hg : OnlyTrace g) (k : Nat)
    (fcw fsw : RamState → BitVec 16) (fcwV : BitVec 16)
    (hfcw : fcw (afterFetches (beforeFetch s) (length + 1)) = fcwV)
    (hrest : fswRest (fsw (afterFetches (beforeFetch s) (length + 1))) = fswRest s.FP87_Status) :
    (x87LdcwEffect p length fcwV).Holds s
      (afterStep s length fun t =>
        x87LdcwOut (g t) (BitVec.add p (BitVec.ofNat 64 length)) k (fcw t) (fsw t)) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  have E : (afterStep s length fun t =>
      x87LdcwOut (g t) (BitVec.add p (BitVec.ofNat 64 length)) k (fcw t) (fsw t)) =
      { (afterStep s length fun t =>
          x87LdcwOut t (BitVec.add p (BitVec.ofNat 64 length)) k (fcw t) (fsw t)) with
        oracle := oracleSkip (g t).oracle k, traceEventsRev := (g t).traceEventsRev } := by
    have E1 : x87LdcwOut (g t) (BitVec.add p (BitVec.ofNat 64 length)) k (fcw t) (fsw t) =
        { x87LdcwOut t (BitVec.add p (BitVec.ofNat 64 length)) k (fcw t) (fsw t) with
          oracle := oracleSkip (g t).oracle k, traceEventsRev := (g t).traceEventsRev } := by
      conv => lhs; rw [hg t]
      rfl
    show finishStep (x87LdcwOut (g t) _ _ _ _) = _
    rw [E1]
    rfl
  rw [E]
  refine Effect.Holds.oracle_trace ?_ _ _
  refine ⟨?_, ?_, trivial, ?_⟩
  · simp [afterStep, finishStep, x87LdcwOut, x87CtlOut, afterFetches, beforeFetch,
      resetStepFields, h.ready.repeatClear, h.ready.msr, x87LdcwEffect, hp]
  · simp only [x87LdcwEffect, Write.AllHold, Operand.read_fcw, Operand.read_fcc]
    exact ⟨hfcw, BitVec.and_zero⟩
  · exact AgreesExcept.afterStep_x87Ldcw s length _ k fcw fsw hrest

/-- The effect of FNSTCW or FNSTSW at `p` of `len` bytes storing the word `v` at `a`: that store,
the condition codes undefined. -/
def x87CtlStoreEffect (p : BitVec 64) (len : Nat) (a : BitVec 64) (v : BitVec 16) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.mem a : Operand 16), v⟩, ⟨(Operand.fcc 0 : Operand 4), 0⟩]

@[simp] theorem x87CtlStoreEffect_components (p : BitVec 64) (len : Nat) (a : BitVec 64)
    (v : BitVec 16) : (x87CtlStoreEffect p len a v).components = [.mem a 2, .fcc, .rip] := by
  simp [x87CtlStoreEffect, Effect.components, Write.component, Operand.component]

theorem x87CtlStoreEffect_avoids {p : BitVec 64} {len : Nat} {a : BitVec 64} {v : BitVec 16}
    {q : BitVec 64} {codeLen : Nat} {bytes : List UInt8} (hd : RangeApart a 2 q codeLen)
    (hl : bytes.length = codeLen) : (x87CtlStoreEffect p len a v).Avoids (codeRange q bytes) := by
  refine Effect.avoids_of_mem (fun c hc hm => ?_) hd hl
  simp only [x87CtlStoreEffect_components, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> first | rfl | exact absurd hm (by simp [Component.isMem])

theorem x87CtlStoreEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (p : BitVec 64) (a : BitVec 64) (v : RamState → BitVec 16) (vV : BitVec 16)
    (hv : v (afterFetches (beforeFetch s) (length + 1)) = vV) (fsw : RamState → BitVec 16)
    (hrest : fswRest (fsw (afterFetches (beforeFetch s) (length + 1))) = fswRest s.FP87_Status) :
    (x87CtlStoreEffect p length a vV).Holds s
      (afterStep s length fun t =>
        (Operand.mem a : Operand 16).write
          (dataAccess (x87CtlOut t (BitVec.add p (BitVec.ofNat 64 length)) 4 (fsw t)) "store")
          (v t)) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  have E : (afterStep s length fun t =>
        (Operand.mem a : Operand 16).write
          (dataAccess (x87CtlOut t (BitVec.add p (BitVec.ofNat 64 length)) 4 (fsw t)) "store")
          (v t)) =
      { (afterStep s length fun t => x87CtlOut t (BitVec.add p (BitVec.ofNat 64 length)) 4 (fsw t))
        with
        oracle := oracleSkip (oracleSkip t.oracle 4) 464
        traceEventsRev := ("isa.memory", "store") :: t.traceEventsRev
        external := memStore s.external a vV } := by
    rw [← hv]
    rfl
  have hag := (AgreesExcept.afterStep_x87Ctl_cc s length (BitVec.add p (BitVec.ofNat 64 length)) 4
    fsw hrest).store_cons a vV (oracleSkip (oracleSkip t.oracle 4) 464)
      (("isa.memory", "store") :: t.traceEventsRev)
  rw [E]
  refine ⟨?_, ?_, (trivial : True), hag⟩
  · show (afterStep s length fun t =>
      x87CtlOut t (BitVec.add p (BitVec.ofNat 64 length)) 4 (fsw t)).RIP = _
    rw [afterStep_x87Ctl_rip h]
    rfl
  · simp only [x87CtlStoreEffect, Write.AllHold, Operand.read_fcc]
    exact ⟨memLoad_memStore _ _ (by decide) (by decide) vV, BitVec.and_zero⟩

/-! ### 80-bit memory operands -/

/-- A byte of `x ++ y` within `y`. -/
theorem extractLsb'_append_lo {m n : Nat} (x : BitVec m) (y : BitVec n) (i : Nat)
    (h : 8 * i + 8 ≤ n) :
    (x ++ y).extractLsb' (8 * i) 8 = y.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split
  · rfl
  · omega

/-- A byte of `x ++ y` within `x`. -/
theorem extractLsb'_append_hi {m n : Nat} (x : BitVec m) (y : BitVec n) (i : Nat)
    (h : n ≤ 8 * i) :
    (x ++ y).extractLsb' (8 * i) 8 = x.extractLsb' (8 * i - n) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split
  · omega
  · congr 1
    omega

theorem storedByte_append_lo {m n : Nat} (x : BitVec m) (y : BitVec n) (i : Nat)
    (h : 8 * i + 8 ≤ n) :
    storedByte (x ++ y) i = storedByte y i := by
  rw [storedByte_extractLsb', extractLsb'_append_lo x y i h, ← storedByte_extractLsb']

theorem storedByte_append_hi {m n : Nat} (x : BitVec m) (y : BitVec n) (i : Nat)
    (hn : n = 64) (h : 8 ≤ i) :
    storedByte (x ++ y) i = storedByte x (i - 8) := by
  subst hn
  rw [storedByte_extractLsb', extractLsb'_append_hi x y i (by omega),
    show 8 * i - 64 = 8 * (i - 8) by omega, ← storedByte_extractLsb']

theorem ofNat_add_eight (a : BitVec 64) (j : Nat) :
    a + 8 + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (8 + j) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

/-- The 80 bits at `a`: the 16 bits at `a + 8` above the 64 bits at `a` (how `FLD m80fp` reads
them). -/
theorem memLoad80 (m : Ram) (a : BitVec 64) :
    memLoad m a 80 = memLoad m (a + 8) 16 ++ memLoad m a 64 := by
  apply memLoad_eq_of_memByte (by decide)
  intro i hi
  by_cases h8 : i < 8
  · rw [storedByte_append_lo _ _ i (by omega), storedByte_memLoad _ _ _ (by omega)]
  · rw [storedByte_append_hi _ _ i rfl (by omega), storedByte_memLoad _ _ _ (by omega),
      ofNat_add_eight, show 8 + (i - 8) = i by omega]

/-- Storing 64 bits at `a`, then 16 at `a + 8` (how `FSTP m80fp` writes) stores their
concatenation at `a`. -/
theorem memStore80 (m : Ram) (a : BitVec 64) (hi : BitVec 16) (lo : BitVec 64) :
    memStore (memStore m a lo) (a + 8) hi = memStore m a (hi ++ lo) := by
  apply Std.ExtHashMap.ext_getElem?
  intro x
  by_cases hx : ∃ i, i < 10 ∧ a + BitVec.ofNat 64 i = x
  · obtain ⟨i, hi10, rfl⟩ := hx
    rw [memStore_getElem?_self _ _ _ (by decide) i (by omega)]
    by_cases h8 : i < 8
    · rw [memStore_getElem?_of_ne, memStore_getElem?_self _ _ _ (by decide) i (by omega),
        storedByte_append_lo _ _ i (by omega)]
      intro j hj he
      rw [ofNat_add_eight] at he
      have := add_ofNat_inj a (by omega) (by omega) he
      omega
    · have h' : a + BitVec.ofNat 64 i = a + 8 + BitVec.ofNat 64 (i - 8) := by
        rw [ofNat_add_eight, show 8 + (i - 8) = i by omega]
      rw [h', memStore_getElem?_self _ _ _ (by decide) (i - 8) (by omega),
        storedByte_append_hi _ _ i rfl (by omega)]
  · have hx' : ∀ i, i < 10 → a + BitVec.ofNat 64 i ≠ x := fun i hi he => hx ⟨i, hi, he⟩
    rw [memStore_getElem?_of_ne, memStore_getElem?_of_ne, memStore_getElem?_of_ne]
    · intro i hi10
      exact hx' i (by omega)
    · intro i hi10
      exact hx' i (by omega)
    · intro j hj he
      rw [ofNat_add_eight] at he
      exact hx' (8 + j) (by omega) he


/-- An 80-bit value is its high 16 bits above its low 64 (as `FSTP m80fp` splits it). -/
theorem extractLsb'_hi_append_lo (x : BitVec 80) :
    x.extractLsb' 64 16 ++ x.extractLsb' 0 64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  · simp only [Nat.zero_add, decide_eq_true (by omega : i < 64), Bool.true_and]
  · simp only [decide_eq_true (by omega : i - 64 < 16), Bool.true_and]
    congr 1
    omega

/-! ### Preconditions after a block -/

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem X87LoadPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {top : BitVec 3}
    {addr : RamState → BitVec 64} {len : Nat} (hx : X87Pre p top s') (ha : AddrObs addr)
    (hr : MemReadable s (addr (e.after s true)) len) : X87LoadPre p top addr len s' :=
  ⟨hx, MemReadable.carry h ho ha hr⟩

@[x86_pre] theorem X87StorePre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {top : BitVec 3} {codeLen : Nat}
    {addr : RamState → BitVec 64} {len : Nat} (hx : X87Pre p top s') (ha : AddrObs addr)
    (hw : MemWritable s (addr (e.after s true)) len)
    (hap : RangeApart (addr (e.after s true)) len p codeLen) :
    X87StorePre p top codeLen addr len s' :=
  ⟨hx, MemWritable.carry h ho ha hw, RangeApart.carry ho ha hap⟩

end Carry

end X86Proofs
