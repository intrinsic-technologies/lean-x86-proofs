import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Program.Compose
import X86Proofs.Program.ReadWrite.String

/-!
# POP to memory: a pop, then a store at an address that follows RSP

`POP r/m` with a memory operand (`8F /0`, lean-x86's `POP_MEMv`) at 64 bits, and at 16 bits after
`66`. lean-x86 computes the operand's address once, sets `Next_IP`, pops (`Operations.POP`: the
`n / 8` bytes at RSP read; it returns the new stack pointer), adds the popped size to the address
if its base is RSP (`Effective_Address`'s `base_uses_rsp`; truncated to the address size), writes
the value popped there, and only then writes RSP. So an address with RSP as its base uses the
incremented RSP, as the SDM specifies for `POP [rsp + d]`.

- `popMemAddr am n next s`: the operand's address in `s` with RSP already incremented, the address
  the value is written to.
- `popMemAdjustedAddr asz baseUsesRsp addr n`: the address as lean-x86 computes it from the
  operand's address `addr` before the pop. `popMemAdjustedAddr_eq_popMemAddr` and
  `popMemAdjustedAddr_eq_popMemAddr32`: it is `popMemAddr` (`popMemAddr32` at address size 32) for
  an encodable operand.
- `popMemState t n am next`: the state the form ends in, from `t` (the state after the address
  computation's fetches): the pop's read, the store, then RSP + `n / 8`.

What a step whose form ends in `popMemState` does: `afterStep_popMem_rip`,
`afterStep_popMem_external` (one store), `Operand.read_afterStep_popMem` (the bytes stored read the
value popped, which is read before the store, so also when the destination overlaps the popped
bytes), `Operand.read_afterStep_popMem_rsp` (RSP + `n / 8`), `AgreesExcept.afterStep_popMem`
(`[.mem a (n / 8), .reg 4, .rip]`), `ReadyToStep.afterStep_popMem`. The effect `popMemEffect`, the
precondition `PopMemPre` (the destination as a store's, `StorePre`, and the bytes at RSP readable)
and `StepEffect.of_popMem` give its triples.

Through an FS/GS segment override (the destination only; the pop reads SS): `popMemAtState t n f
am next` stores at `f` of the offset (`segAddr` of the decode context; `popMemState` is it with
the identity, `popMemState_eq_at`), with the same facts (`…_popMemAt…`); `popMemSegEffect`,
`PopMemSegPre` (`SegStorePre` at `base + popMemAddr …`) and `StepEffect.of_popMemSeg`.

At address size 32 (`67`): `popMemAddr32` (`popMemAddr`'s low 32 bits, zero-extended), the
precondition `PopMemA32Pre`, the effect `popMemA32Effect` and `StepEffect.of_popMem32` (the form
ends in `popMemAtState` with the truncation as `f`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The address `POP m` (`n` bits) writes to, in `s`: the operand's address computed with RSP
already incremented by `n / 8` (`next` is the RIP-relative base). -/
def popMemAddr (am : AddrMode) (n : Nat) (next : BitVec 64) (s : RamState) : BitVec 64 :=
  am.addr ((Operand.reg 4 : Operand 64).write s (stackPtr s + BitVec.ofNat 64 (n / 8))) next

/-- The address lean-x86's `POP m` (`n` bits) stores at, from the operand's address `addr`
computed before the pop: with base RSP (`baseUsesRsp`), `addr` plus the popped size, truncated
to the address size `asz` (64 or 32) and zero-extended; else `addr`. -/
def popMemAdjustedAddr (asz : Nat) (baseUsesRsp : Bool) (addr : BitVec 64) (n : Nat) : BitVec 64 :=
  if baseUsesRsp then ((addr + BitVec.ofNat 64 (n / 8)).setWidth asz).setWidth 64 else addr

/-- The state `POP m` (`n` bits, operand `am`, `Next_IP` = `next`) ends in, from the state `t` after
its address computation, storing at `f` of the offset `popMemAddr` (`f` is the linear address of an
offset: `segAddr` of the decode context, the identity without a segment override): the pop's read
(`dataAccess … "load"`), the store of the `n / 8` bytes read at RSP, then RSP := RSP + `n / 8`. -/
def popMemAtState (t : RamState) (n : Nat) (f : BitVec 64 → BitVec 64) (am : AddrMode)
    (next : BitVec 64) : RamState :=
  (Operand.reg 4 : Operand 64).write
    ((Operand.mem (f (popMemAddr am n next t)) : Operand n).write
      (dataAccess (dataAccess (withNextIP t next) "load") "store")
      ((Operand.mem (stackPtr t) : Operand n).read t))
    (stackPtr t + BitVec.ofNat 64 (n / 8))

/-- `popMemAtState` without a segment override: the store at `popMemAddr`. -/
def popMemState (t : RamState) (n : Nat) (am : AddrMode) (next : BitVec 64) : RamState :=
  popMemAtState t n (fun a => a) am next

theorem popMemState_eq_at (t : RamState) (n : Nat) (am : AddrMode) (next : BitVec 64) :
    popMemState t n am next = popMemAtState t n (fun a => a) am next := rfl

/-- `popMemAddr` is the same in any state with the same registers. -/
theorem popMemAddr_of_gpr (am : AddrMode) (n : Nat) (next : BitVec 64) {s t : RamState}
    (h : t.GPR = s.GPR) : popMemAddr am n next t = popMemAddr am n next s :=
  AddrMode.addr_of_gpr (by simp [Operand.write, stackPtr, h]) next

/-- `popMemAddr` reads only the observable state. -/
theorem popMemAddr_obs (am : AddrMode) (n : Nat) (next : BitVec 64) {t t' : RamState}
    (h : Obs t t') : popMemAddr am n next t = popMemAddr am n next t' := by
  have hsp : stackPtr t = stackPtr t' := by simp [stackPtr, h.gpr]
  unfold popMemAddr
  rw [hsp]
  exact AddrMode.addr_obs (h.write _ _) am next

/-- The address lean-x86 computes for `POP m`'s store at address size 64 (`popMemAdjustedAddr`
of the operand's address before the pop) is `popMemAddr`, for an encodable operand. -/
theorem popMemAdjustedAddr_eq_popMemAddr (am : AddrMode) (hv : am.Valid) (n : Nat)
    (next : BitVec 64) (s : RamState) :
    popMemAdjustedAddr 64 am.baseUsesRsp (am.addr s next) n = popMemAddr am n next s := by
  unfold popMemAdjustedAddr popMemAddr
  rw [show stackPtr s = AddrMode.reg64 4 s from rfl, AddrMode.addr_write_rsp_add am hv]
  cases am.baseUsesRsp <;> simp

/-! ### After a POP-to-memory step -/

theorem afterStep_popMemAt_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (f : BitVec 64 → BitVec 64) (am : AddrMode) (nextIP : BitVec 64) :
    (afterStep s length fun t => popMemAtState t n f am nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, popMemAtState, withNextIP, Operand.write, dataAccess,
    afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Memory after a POP-to-memory step storing at `f`: the value popped stored at
`f (popMemAddr …)`. -/
@[simp] theorem afterStep_popMemAt_external (s : RamState) (length n : Nat)
    (f : BitVec 64 → BitVec 64) (am : AddrMode) (nextIP : BitVec 64) :
    (afterStep s length fun t => popMemAtState t n f am nextIP).external =
      memStore s.external (f (popMemAddr am n nextIP s))
        ((Operand.mem (stackPtr s) : Operand n).read s) := by
  simp only [afterStep, finishStep, popMemAtState, Operand.write]
  rw [popMemAddr_of_gpr am n nextIP (s := s) rfl]
  rfl

theorem Operand.read_afterStep_popMemAt (s : RamState) (length n : Nat) (hn : n % 8 = 0)
    (h128 : n ≤ 128) (f : BitVec 64 → BitVec 64) (am : AddrMode) (nextIP : BitVec 64) :
    (Operand.mem (f (popMemAddr am n nextIP s)) : Operand n).read
      (afterStep s length fun t => popMemAtState t n f am nextIP) =
      (Operand.mem (stackPtr s) : Operand n).read s := by
  simp only [Operand.read, afterStep_popMemAt_external]
  exact memLoad_memStore _ _ hn h128 _

theorem Operand.read_afterStep_popMemAt_rsp (s : RamState) (length n : Nat)
    (f : BitVec 64 → BitVec 64) (am : AddrMode) (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => popMemAtState t n f am nextIP) =
      stackPtr s + BitVec.ofNat 64 (n / 8) := by
  rw [Operand.read_afterStep]
  exact Operand.read_write_reg64_self _ 4 _

/-- A POP-to-memory step storing at `f` changes only the `n / 8` bytes at `f (popMemAddr …)`,
RSP and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_popMemAt (s : RamState) (length n : Nat)
    (f : BitVec 64 → BitVec 64) (am : AddrMode) (nextIP : BitVec 64) :
    AgreesExcept [.mem (f (popMemAddr am n nextIP s)) (n / 8), .reg 4, .rip] s
      (afterStep s length fun t => popMemAtState t n f am nextIP) := by
  have ha : popMemAddr am n nextIP (afterFetches (beforeFetch s) (length + 1)) =
      popMemAddr am n nextIP s := popMemAddr_of_gpr am n nextIP rfl
  have hall := AgreesExcept.of_afterStep s length (fun t => popMemAtState t n f am nextIP)
    (((((AgreesExcept.of_nextIP _ nextIP).trans (AgreesExcept.of_dataAccess _ "load")).trans
      (AgreesExcept.of_dataAccess _ "store")).trans
      (AgreesExcept.write_mem _ _ _)).trans (AgreesExcept.write_reg _ 4 _))
  rw [ha] at hall
  exact hall.mono (by simp)

theorem ReadyToStep.afterStep_popMemAt [Bindings] {s : RamState} (h : ReadyToStep s)
    (length n : Nat) (f : BitVec 64 → BitVec 64) (am : AddrMode) (nextIP : BitVec 64)
    (hlow : (f (popMemAddr am n nextIP s)).toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart (f (popMemAddr am n nextIP s)).toNat (n / 8)) :
    ReadyToStep (afterStep s length fun t => popMemAtState t n f am nextIP) :=
  h.of_agreesExcept (AgreesExcept.afterStep_popMemAt s length n f am nextIP) (by
    rw [afterStep_popMemAt_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables)

/-- After a POP-to-memory step, RIP is `nextIP`. -/
theorem afterStep_popMem_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length n : Nat)
    (am : AddrMode) (nextIP : BitVec 64) :
    (afterStep s length fun t => popMemState t n am nextIP).RIP = nextIP :=
  afterStep_popMemAt_rip h length n _ am nextIP

/-- Memory after a POP-to-memory step: the value popped stored at `popMemAddr`. -/
@[simp] theorem afterStep_popMem_external (s : RamState) (length n : Nat) (am : AddrMode)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => popMemState t n am nextIP).external =
      memStore s.external (popMemAddr am n nextIP s)
        ((Operand.mem (stackPtr s) : Operand n).read s) :=
  afterStep_popMemAt_external s length n _ am nextIP

/-- After a POP-to-memory step, the bytes at `popMemAddr` hold the bytes that were at the old
RSP. -/
theorem Operand.read_afterStep_popMem (s : RamState) (length n : Nat) (hn : n % 8 = 0)
    (h128 : n ≤ 128) (am : AddrMode) (nextIP : BitVec 64) :
    (Operand.mem (popMemAddr am n nextIP s) : Operand n).read
      (afterStep s length fun t => popMemState t n am nextIP) =
      (Operand.mem (stackPtr s) : Operand n).read s :=
  Operand.read_afterStep_popMemAt s length n hn h128 (fun a => a) am nextIP

/-- After a POP-to-memory step, RSP is the old RSP + `n / 8`. -/
theorem Operand.read_afterStep_popMem_rsp (s : RamState) (length n : Nat) (am : AddrMode)
    (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => popMemState t n am nextIP) =
      stackPtr s + BitVec.ofNat 64 (n / 8) :=
  Operand.read_afterStep_popMemAt_rsp s length n _ am nextIP

/-- A POP-to-memory step changes only the `n / 8` bytes at `popMemAddr`, RSP and RIP (besides the
bookkeeping). -/
theorem AgreesExcept.afterStep_popMem (s : RamState) (length n : Nat) (am : AddrMode)
    (nextIP : BitVec 64) :
    AgreesExcept [.mem (popMemAddr am n nextIP s) (n / 8), .reg 4, .rip] s
      (afterStep s length fun t => popMemState t n am nextIP) :=
  AgreesExcept.afterStep_popMemAt s length n (fun a => a) am nextIP

/-- Preservation for a POP to memory: if the bytes written lie below 4 GiB and outside the page
tables, the state after the step is ready to step again. -/
theorem ReadyToStep.afterStep_popMem [Bindings] {s : RamState} (h : ReadyToStep s)
    (length n : Nat) (am : AddrMode) (nextIP : BitVec 64)
    (hlow : (popMemAddr am n nextIP s).toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart (popMemAddr am n nextIP s).toNat (n / 8)) :
    ReadyToStep (afterStep s length fun t => popMemState t n am nextIP) :=
  ReadyToStep.afterStep_popMemAt h length n (fun a => a) am nextIP hlow htables

/-! ### Effect and triple -/

/-- The precondition of a POP-to-memory triple at `p` (`n` bits, an instruction of `len` bytes,
operand `am`): the destination, `popMemAddr`, as a store's (`StorePre`: RIP = `p`, writable in
place, apart from the instruction), and the `n / 8` bytes at RSP readable. -/
abbrev PopMemPre (p : BitVec 64) (len n : Nat) (am : AddrMode) (s : RamState) : Prop :=
  StorePre p len (popMemAddr am n (p + BitVec.ofNat 64 len)) (n / 8) s ∧
    MemReadable s (stackPtr s) (n / 8)

/-- The effect of `POP m` (`n` bits) at `p`, for an encoding of `len` bytes: RIP = `p + len`, the
`n / 8` bytes at `popMemAddr` (the address with RSP incremented) set to the `n / 8` bytes at the
old RSP, RSP := RSP + `n / 8`. -/
def popMemEffect (p : BitVec 64) (len n : Nat) (am : AddrMode) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.mem (popMemAddr am n (p + BitVec.ofNat 64 len) s) : Operand n),
      (Operand.mem (stackPtr s) : Operand n).read s⟩,
    ⟨(Operand.reg 4 : Operand 64), stackPtr s + BitVec.ofNat 64 (n / 8)⟩]

@[simp] theorem popMemEffect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (s : RamState) :
    (popMemEffect p len n am s).components =
      [.mem (popMemAddr am n (p + BitVec.ofNat 64 len) s) (n / 8), .reg 4, .rip] := rfl

/-- A POP-to-memory effect avoids the instruction's code when its precondition holds. -/
theorem popMemEffect_avoids {p : BitVec 64} {bytes : List UInt8} {len n : Nat}
    (hlen : bytes.length = len) (am : AddrMode) {s : RamState} (h : PopMemPre p len n am s) :
    (popMemEffect p len n am s).Avoids (codeRange p bytes) := by
  subst hlen
  intro x hx c hc hcov
  rw [popMemEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · obtain ⟨i, hi, hxe⟩ := hcov
    obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
    exact h.1.code i hi j hj (hxe.symm.trans hxj)
  · exact hcov
  · exact hcov

/-- A POP-to-memory effect reads only the observable state (for `n` a supported memory size). -/
theorem popMemEffect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} (hn : n % 8 = 0) :
    Effect.Local (popMemEffect p len n am) := by
  refine ⟨fun _ _ _ => rfl, fun t t' h => ?_, fun _ _ _ => rfl, fun t t' _ i hi => ?_,
    fun t => ?_⟩
  · have hsp : stackPtr t = stackPtr t' := by simp [stackPtr, h.gpr]
    simp only [popMemEffect, popMemAddr_obs am n _ h, h.read_mem, hsp]
  · simp only [popMemEffect, Effect.flag]
    rw [hi]
  · simp [popMemEffect, Write.Full, Operand.Full, hn]

attribute [x86_compose] popMemEffect popMemAddr

/--
The step of a POP-to-memory form at `p` with its effect, from its step theorem. If from every
ready state with the instruction `bytes` at `p` and `PopMemPre`, one `step` runs the form, ending
in `popMemState` with `Next_IP` = `p + len`, then that step reaches a ready state with the effect
`popMemEffect p len n am`.
-/
theorem StepEffect.of_popMem [Bindings] {p : BitVec 64} {bytes : List UInt8} {len n : Nat}
    (hn : n % 8 = 0) (h128 : n ≤ 128) (am : AddrMode)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → PopMemPre p len n am s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        popMemState t n am (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect (PopMemPre p len n am) (codeRange p bytes) (popMemEffect p len n am) := by
  intro s h hcode hpre
  exact ⟨_, hstep s h hcode hpre,
    ReadyToStep.afterStep_popMem h _ _ _ _ hpre.1.write.low hpre.1.write.tables,
    ⟨afterStep_popMem_rip h _ _ _ _, ⟨Operand.read_afterStep_popMem s _ _ hn h128 _ _,
      Operand.read_afterStep_popMem_rsp s _ _ _ _⟩, trivial,
      AgreesExcept.afterStep_popMem s _ _ _ _⟩⟩

/-! ### Through an FS/GS segment override -/

/-- The precondition of a POP-to-memory triple whose destination has a segment override `r` (FS
or GS) with base `base`: the destination `base + popMemAddr …` as a store's (`SegStorePre`, with
the segment ready), and the `n / 8` bytes at RSP readable (the pop reads SS, which takes no
override). -/
abbrev PopMemSegPre (p : BitVec 64) (len n : Nat) (r : SegReg) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Prop :=
  SegStorePre p len r base (popMemAddr am n (p + BitVec.ofNat 64 len)) (n / 8) s ∧
    MemReadable s (stackPtr s) (n / 8)

/-- `popMemEffect` with the destination at `base + popMemAddr …` (an FS or GS override). -/
def popMemSegEffect (p : BitVec 64) (len n : Nat) (base : BitVec 64) (am : AddrMode)
    (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.mem (base + popMemAddr am n (p + BitVec.ofNat 64 len) s) : Operand n),
      (Operand.mem (stackPtr s) : Operand n).read s⟩,
    ⟨(Operand.reg 4 : Operand 64), stackPtr s + BitVec.ofNat 64 (n / 8)⟩]

@[simp] theorem popMemSegEffect_components (p : BitVec 64) (len n : Nat) (base : BitVec 64)
    (am : AddrMode) (s : RamState) :
    (popMemSegEffect p len n base am s).components =
      [.mem (base + popMemAddr am n (p + BitVec.ofNat 64 len) s) (n / 8), .reg 4, .rip] := rfl

theorem popMemSegEffect_avoids {p : BitVec 64} {bytes : List UInt8} {len n : Nat}
    (hlen : bytes.length = len) {r : SegReg} {base : BitVec 64} (am : AddrMode) {s : RamState}
    (h : PopMemSegPre p len n r base am s) :
    (popMemSegEffect p len n base am s).Avoids (codeRange p bytes) := by
  subst hlen
  intro x hx c hc hcov
  rw [popMemSegEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · obtain ⟨i, hi, hxe⟩ := hcov
    obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
    exact h.1.store.code i hi j hj (hxe.symm.trans hxj)
  · exact hcov
  · exact hcov

theorem popMemSegEffect_local {p : BitVec 64} {len n : Nat} {base : BitVec 64} {am : AddrMode}
    (hn : n % 8 = 0) : Effect.Local (popMemSegEffect p len n base am) := by
  refine ⟨fun _ _ _ => rfl, fun t t' h => ?_, fun _ _ _ => rfl, fun t t' _ i hi => ?_,
    fun t => ?_⟩
  · have hsp : stackPtr t = stackPtr t' := by simp [stackPtr, h.gpr]
    simp only [popMemSegEffect, popMemAddr_obs am n _ h, h.read_mem, hsp]
  · simp only [popMemSegEffect, Effect.flag]
    rw [hi]
  · simp [popMemSegEffect, Write.Full, Operand.Full, hn]

attribute [x86_compose] popMemSegEffect

/-- `StepEffect.of_popMem` through an FS/GS override with base `base`: a step whose form ends in
`popMemAtState` storing at `base + ·` has the effect `popMemSegEffect`. -/
theorem StepEffect.of_popMemSeg [Bindings] {p : BitVec 64} {bytes : List UInt8} {len n : Nat}
    (hn : n % 8 = 0) (h128 : n ≤ 128) (r : SegReg) (base : BitVec 64) (am : AddrMode)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s →
      PopMemSegPre p len n r base am s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        popMemAtState t n (fun a => base + a) am (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect (PopMemSegPre p len n r base am) (codeRange p bytes)
      (popMemSegEffect p len n base am) := by
  intro s h hcode hpre
  exact ⟨_, hstep s h hcode hpre,
    ReadyToStep.afterStep_popMemAt h _ _ _ _ _ hpre.1.store.write.low hpre.1.store.write.tables,
    ⟨afterStep_popMemAt_rip h _ _ _ _ _, ⟨Operand.read_afterStep_popMemAt s _ _ hn h128 _ _ _,
      Operand.read_afterStep_popMemAt_rsp s _ _ _ _ _⟩, trivial,
      AgreesExcept.afterStep_popMemAt s _ _ _ _ _⟩⟩

/-! ### At address size 32 (`67`)

Behind an address-size prefix `67` both address computations are at address size 32, so the
destination is the low 32 bits of `popMemAddr`, zero-extended (`popMemAddr32`, as
`AddrMode.addr32`); the pop still reads and writes the 64-bit RSP. The form ends in
`popMemAtState` with the truncation as `f`. -/

/-- The address `POP m` (`n` bits) writes to at address size 32 in `s`: `popMemAddr`'s low 32
bits, zero-extended. -/
def popMemAddr32 (am : AddrMode) (n : Nat) (next : BitVec 64) (s : RamState) : BitVec 64 :=
  ((popMemAddr am n next s).setWidth 32).setWidth 64

/-- The address lean-x86 computes for `POP m`'s store at address size 32 (`popMemAdjustedAddr`
of the operand's 32-bit address before the pop) is `popMemAddr32`, for an encodable operand. -/
theorem popMemAdjustedAddr_eq_popMemAddr32 (am : AddrMode) (hv : am.Valid) (n : Nat)
    (next : BitVec 64) (s : RamState) :
    popMemAdjustedAddr 32 am.baseUsesRsp (am.addr32 s next) n = popMemAddr32 am n next s := by
  unfold popMemAdjustedAddr popMemAddr32 popMemAddr AddrMode.addr32
  rw [show stackPtr s = AddrMode.reg64 4 s from rfl, AddrMode.addr_write_rsp_add am hv]
  cases am.baseUsesRsp
  · simp
  · simp only [↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- `popMemAddr32` reads only the observable state. -/
theorem popMemAddr32_obs (am : AddrMode) (n : Nat) (next : BitVec 64) {t t' : RamState}
    (h : Obs t t') : popMemAddr32 am n next t = popMemAddr32 am n next t' := by
  simp only [popMemAddr32, popMemAddr_obs am n next h]

/-- The precondition of a POP-to-memory triple at address size 32: `PopMemPre` with the
destination at `popMemAddr32`. -/
abbrev PopMemA32Pre (p : BitVec 64) (len n : Nat) (am : AddrMode) (s : RamState) : Prop :=
  StorePre p len (popMemAddr32 am n (p + BitVec.ofNat 64 len)) (n / 8) s ∧
    MemReadable s (stackPtr s) (n / 8)

/-- `popMemEffect` with the destination at `popMemAddr32` (address size 32). -/
def popMemA32Effect (p : BitVec 64) (len n : Nat) (am : AddrMode) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.mem (popMemAddr32 am n (p + BitVec.ofNat 64 len) s) : Operand n),
      (Operand.mem (stackPtr s) : Operand n).read s⟩,
    ⟨(Operand.reg 4 : Operand 64), stackPtr s + BitVec.ofNat 64 (n / 8)⟩]

@[simp] theorem popMemA32Effect_components (p : BitVec 64) (len n : Nat) (am : AddrMode)
    (s : RamState) :
    (popMemA32Effect p len n am s).components =
      [.mem (popMemAddr32 am n (p + BitVec.ofNat 64 len) s) (n / 8), .reg 4, .rip] := rfl

/-- A POP-to-memory effect at address size 32 avoids the instruction's code when its precondition
holds. -/
theorem popMemA32Effect_avoids {p : BitVec 64} {bytes : List UInt8} {len n : Nat}
    (hlen : bytes.length = len) (am : AddrMode) {s : RamState} (h : PopMemA32Pre p len n am s) :
    (popMemA32Effect p len n am s).Avoids (codeRange p bytes) := by
  subst hlen
  intro x hx c hc hcov
  rw [popMemA32Effect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · obtain ⟨i, hi, hxe⟩ := hcov
    obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
    exact h.1.code i hi j hj (hxe.symm.trans hxj)
  · exact hcov
  · exact hcov

/-- A POP-to-memory effect at address size 32 reads only the observable state. -/
theorem popMemA32Effect_local {p : BitVec 64} {len n : Nat} {am : AddrMode} (hn : n % 8 = 0) :
    Effect.Local (popMemA32Effect p len n am) := by
  refine ⟨fun _ _ _ => rfl, fun t t' h => ?_, fun _ _ _ => rfl, fun t t' _ i hi => ?_,
    fun t => ?_⟩
  · have hsp : stackPtr t = stackPtr t' := by simp [stackPtr, h.gpr]
    simp only [popMemA32Effect, popMemAddr32_obs am n _ h, h.read_mem, hsp]
  · simp only [popMemA32Effect, Effect.flag]
    rw [hi]
  · simp [popMemA32Effect, Write.Full, Operand.Full, hn]

attribute [x86_compose] popMemA32Effect popMemAddr32

/-- `StepEffect.of_popMem` at address size 32: a step whose form ends in `popMemAtState` storing
at the low 32 bits of the offset, zero-extended, has the effect `popMemA32Effect`. -/
theorem StepEffect.of_popMem32 [Bindings] {p : BitVec 64} {bytes : List UInt8} {len n : Nat}
    (hn : n % 8 = 0) (h128 : n ≤ 128) (am : AddrMode)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → PopMemA32Pre p len n am s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        popMemAtState t n (fun a => (a.setWidth 32).setWidth 64) am
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect (PopMemA32Pre p len n am) (codeRange p bytes) (popMemA32Effect p len n am) := by
  intro s h hcode hpre
  let f : BitVec 64 → BitVec 64 := fun a => (a.setWidth 32).setWidth 64
  exact ⟨_, hstep s h hcode hpre,
    ReadyToStep.afterStep_popMemAt h _ _ f _ _ hpre.1.write.low hpre.1.write.tables,
    ⟨afterStep_popMemAt_rip h _ _ f _ _, ⟨Operand.read_afterStep_popMemAt s _ _ hn h128 f _ _,
      Operand.read_afterStep_popMemAt_rsp s _ _ f _ _⟩, trivial,
      AgreesExcept.afterStep_popMemAt s _ _ f _ _⟩⟩

end X86Proofs
