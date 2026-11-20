import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Core.Lanes

/-!
# Masked stores: a byte write per selected byte

Shared by MASKMOVDQU and MASKMOVQ, which store the bytes of a register (XMM, 16 bytes; MMX, 8
bytes) selected by a mask (bit 7 of each byte of a second register of the same kind) to the bytes
at RDI, one `Logical_Mem_Write` of one byte per selected byte, after checking that all the bytes
can be written. The number of writes, and so the oracle bits and the `store` trace events, depend
on the mask; the bytes not selected are not written at all.

The definitions and lemmas with an `N` suffix are stated for an `n`-bit register (`n / 8` bytes);
the ones without are MASKMOVDQU's, their 128-bit (16-byte) instances.

- `maskBitN mask i`: byte `i` is selected (bit 7 of byte `i` of `mask`).
- `maskMemN m a src mask`: memory `m` after the selected bytes of `src` are stored at `a + i`.
- `maskByteStoreN a src mask i t`: the state after byte `i`'s write (if selected), as lean-x86's
  loop body leaves it; `maskStoresN a src mask t`: after all `n / 8`, in closed form (memory
  `maskMemN`, the oracle and the trace advanced once per selected byte), which is the fold of
  `maskByteStoreN` (`maskStoresN_eq_foldl`).
- `maskMemN_getElem?_self`, `maskMemN_getElem?_of_ne`, `maskMemN_isSome`: the bytes of
  `maskMemN`; `memLoad_maskMemN`: the `n / 8` bytes at `a` read back as the selected bytes of
  `src` merged with the old ones (`maskMergeN`).
- `maskStateN a src mask ip f t`: the state after a masked-store form from `t` (`Next_IP` set,
  the oracle advanced by `f` for the writability checks, then the byte stores). After a step
  ending there: `afterStep_maskStateN_rip`, `Operand.read_afterStep_maskStateN`,
  `ReadyToStep.afterStep_maskStateN`, `AgreesExcept.afterStep_maskStateN` (only the `n / 8`
  bytes and RIP change), and `StepEffect.of_maskStateN`: its step with the `storeEffect` of the
  merged bytes. `StepEffect.of_maskStateN_mmx`: the same for a form that first enters MMX mode
  (`mmxEnter`, MASKMOVQ), with `Effect.withMmx`.
- MASKMOVDQU (16 bytes, two writability checks): `maskBit`, `maskMem`, `maskStores`,
  `maskmovState`, `maskMerge` and their lemmas (`afterStep_maskmov_rip`, …,
  `StepEffect.of_maskmov`). MASKMOVQ (8 bytes, one check, MMX mode): `maskmovqState`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Byte `i` of an `n`-bit value is selected by `mask`: bit 7 of byte `i` of `mask` is set. -/
def maskBitN {n : Nat} (mask : BitVec n) (i : Nat) : Bool := (lane 8 mask i).msb

/-- The memory step of byte `i`: byte `i` of `src` stored at `a + i` if `mask` selects it. -/
def maskMemByteN {n : Nat} (a : BitVec 64) (src mask : BitVec n) (m : Ram) (i : Nat) : Ram :=
  if maskBitN mask i then memStore m (a + BitVec.ofNat 64 i) (lane 8 src i) else m

/-- Memory `m` after the bytes of `src` that `mask` selects are stored at `a`, `a + 1`, …,
`a + n / 8 - 1`, one byte at a time from byte 0 up. -/
def maskMemN {n : Nat} (m : Ram) (a : BitVec 64) (src mask : BitVec n) : Ram :=
  (List.range (n / 8)).foldl (maskMemByteN a src mask) m

/-- The state after the write of byte `i` (if `mask` selects it), as lean-x86's loop body leaves
it: a one-byte data write at `a + i` with its bookkeeping (`dataAccess t "store"`), or nothing. -/
def maskByteStoreN {n : Nat} (a : BitVec 64) (src mask : BitVec n) (i : Nat) (t : RamState) :
    RamState :=
  if maskBitN mask i then
    (Operand.mem (a + BitVec.ofNat 64 i) : Operand 8).write (dataAccess t "store") (lane 8 src i)
  else t

/-- The oracle step of byte `i`: the 464 bits of a data write if `mask` selects it. -/
def maskOracleByteN {n : Nat} (mask : BitVec n) (o : X86.Runtime.Oracle) (i : Nat) :
    X86.Runtime.Oracle :=
  if maskBitN mask i then oracleSkip o 464 else o

/-- The trace step of byte `i`: a `store` event if `mask` selects it. -/
def maskTraceByteN {n : Nat} (mask : BitVec n) (r : List (String × String)) (i : Nat) :
    List (String × String) :=
  if maskBitN mask i then ("isa.memory", "store") :: r else r

/-- The state after the `n / 8` byte writes of a masked store from `t`, in closed form: memory is
`maskMemN`, and the oracle and the trace advance once per selected byte; nothing else changes. -/
def maskStoresN {n : Nat} (a : BitVec 64) (src mask : BitVec n) (t : RamState) : RamState :=
  { t with
    external := maskMemN t.external a src mask
    oracle := (List.range (n / 8)).foldl (maskOracleByteN mask) t.oracle
    traceEventsRev := (List.range (n / 8)).foldl (maskTraceByteN mask) t.traceEventsRev }

theorem foldl_maskByteStoreN {n : Nat} (a : BitVec 64) (src mask : BitVec n) (l : List Nat)
    (t : RamState) :
    l.foldl (fun u i => maskByteStoreN a src mask i u) t =
      { t with
        external := l.foldl (maskMemByteN a src mask) t.external
        oracle := l.foldl (maskOracleByteN mask) t.oracle
        traceEventsRev := l.foldl (maskTraceByteN mask) t.traceEventsRev } := by
  induction l generalizing t with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih]
    by_cases hb : maskBitN mask i <;>
      simp [maskByteStoreN, maskMemByteN, maskOracleByteN, maskTraceByteN, hb, Operand.write,
        dataAccess]

/-- The closed form is lean-x86's loop: the fold of `maskByteStoreN` over bytes 0 to
`n / 8 - 1`. -/
theorem maskStoresN_eq_foldl {n : Nat} (a : BitVec 64) (src mask : BitVec n) (t : RamState) :
    (List.range (n / 8)).foldl (fun u i => maskByteStoreN a src mask i u) t =
      maskStoresN a src mask t :=
  foldl_maskByteStoreN a src mask _ t

/-! ### The bytes of a masked store -/

theorem foldl_maskMemByteN_of_ne {n : Nat} (a : BitVec 64) (src mask : BitVec n) (l : List Nat)
    (m : Ram) (x : BitVec 64) (hx : ∀ i ∈ l, a + BitVec.ofNat 64 i ≠ x) :
    (l.foldl (maskMemByteN a src mask) m)[x]? = m[x]? := by
  induction l generalizing m with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih _ fun j hj => hx j (List.mem_cons_of_mem _ hj)]
    unfold maskMemByteN
    split
    · exact memStore_getElem?_of_ne _ _ _ _ fun k hk => by
        rw [show k = 0 by omega]
        simpa using hx i List.mem_cons_self
    · rfl

/-- A byte outside the `n / 8` bytes at `a` is unchanged by a masked store. -/
theorem maskMemN_getElem?_of_ne {n : Nat} (m : Ram) (a : BitVec 64) (src mask : BitVec n)
    (x : BitVec 64) (hx : ∀ i < n / 8, a + BitVec.ofNat 64 i ≠ x) :
    (maskMemN m a src mask)[x]? = m[x]? :=
  foldl_maskMemByteN_of_ne a src mask _ m x fun i hi => hx i (List.mem_range.mp hi)

theorem foldl_maskMemByteN_self {n : Nat} (hn : n ≤ 128) (a : BitVec 64) (src mask : BitVec n)
    (l : List Nat) (m : Ram) (j : Nat) (hj : j < n / 8) (hl : ∀ i ∈ l, i < n / 8) :
    (l.foldl (maskMemByteN a src mask) m)[a + BitVec.ofNat 64 j]? =
      if j ∈ l ∧ maskBitN mask j = true then some (storedByte (lane 8 src j) 0)
      else m[a + BitVec.ofNat 64 j]? := by
  induction l generalizing m with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih _ fun k hk => hl k (List.mem_cons_of_mem _ hk)]
    have hi := hl i List.mem_cons_self
    by_cases hjl : j ∈ l ∧ maskBitN mask j = true
    · simp [hjl]
    · simp only [hjl, ite_false]
      unfold maskMemByteN
      by_cases hij : i = j
      · subst hij
        by_cases hb : maskBitN mask i
        · have := memStore_getElem?_self m (a + BitVec.ofNat 64 i) (lane 8 src i) (by decide) 0
            (by decide)
          simp only [BitVec.add_zero] at this
          simp [hb, this]
        · simp [hb]
      · have hne : ¬ (j ∈ i :: l ∧ maskBitN mask j = true) := by
          rintro ⟨hm, hb⟩
          rcases List.mem_cons.mp hm with h | h
          · exact hij h.symm
          · exact hjl ⟨h, hb⟩
        simp only [hne, ite_false]
        split
        · refine memStore_getElem?_of_ne _ _ _ _ fun k hk he => hij ?_
          rw [show k = 0 by omega] at he
          simp only [BitVec.add_zero] at he
          exact add_ofNat_inj a (by omega) (by omega) he.symm |>.symm
        · rfl

/-- Byte `j` (`j < n / 8`) of a masked store at `a`: byte `j` of `src` if `mask` selects it, else
the old byte. -/
theorem maskMemN_getElem?_self {n : Nat} (hn : n ≤ 128) (m : Ram) (a : BitVec 64)
    (src mask : BitVec n) (j : Nat) (hj : j < n / 8) :
    (maskMemN m a src mask)[a + BitVec.ofNat 64 j]? =
      if maskBitN mask j then some (storedByte (lane 8 src j) 0)
      else m[a + BitVec.ofNat 64 j]? := by
  rw [maskMemN, foldl_maskMemByteN_self hn a src mask _ m j hj fun i hi => List.mem_range.mp hi]
  simp [List.mem_range, hj]

/-- A masked store keeps every byte of RAM present. -/
theorem maskMemN_isSome {n : Nat} (m : Ram) (a : BitVec 64) (src mask : BitVec n) (x : BitVec 64)
    (h : (m[x]?).isSome) : ((maskMemN m a src mask)[x]?).isSome := by
  unfold maskMemN
  generalize List.range (n / 8) = l
  induction l generalizing m with
  | nil => exact h
  | cons i l ih =>
    rw [List.foldl_cons]
    apply ih
    unfold maskMemByteN
    split
    · exact memStore_isSome _ _ _ x h
    · exact h

/-- A masked store keeps the identity-mapped page tables if its `n / 8` bytes lie below 4 GiB and
outside the page-table frames. -/
theorem IdentityPageTableMemory.maskMemN {m : Ram} (h : IdentityPageTableMemory m) {n : Nat}
    (a : BitVec 64) (src mask : BitVec n) (hlow : a.toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart a.toNat (n / 8)) :
    IdentityPageTableMemory (X86Proofs.maskMemN m a src mask) := by
  unfold X86Proofs.maskMemN
  have hl : ∀ i ∈ List.range (n / 8), i < n / 8 := fun i hi => List.mem_range.mp hi
  generalize List.range (n / 8) = l at hl
  induction l generalizing m with
  | nil => exact h
  | cons i l ih =>
    rw [List.foldl_cons]
    apply ih _ fun k hk => hl k (List.mem_cons_of_mem _ hk)
    have hi := hl i List.mem_cons_self
    have hai : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    unfold maskMemByteN
    split
    · exact IdentityPageTableMemory.memStore h _ _ (by rw [hai]; omega) (by rw [hai]; omega)
    · exact h

/-- The merged bytes a masked store leaves at its address: lane `i` of `src` where `mask` selects
it, else lane `i` of the old value `old`. -/
def maskMergeN {n : Nat} (src mask old : BitVec n) : BitVec n :=
  ofLanes n 8 fun i => if maskBitN mask i then lane 8 src i else lane 8 old i

/-- The `n / 8` bytes at `a` after a masked store, read back: lane `i` is lane `i` of `src` if
`mask` selects it, else the old lane. -/
theorem memLoad_maskMemN {n : Nat} (hn : n % 8 = 0) (h128 : n ≤ 128) (m : Ram) (a : BitVec 64)
    (src mask : BitVec n) :
    memLoad (maskMemN m a src mask) a n = maskMergeN src mask (memLoad m a n) := by
  apply memLoad_eq_of_memByte hn
  intro i hi
  have hl : ∀ v : BitVec n, v.extractLsb' (8 * i) 8 = lane 8 v i := fun v => by
    rw [lane, Nat.mul_comm]
  rw [maskMergeN, storedByte_extractLsb', hl, lane_ofLanes _ _ (by omega), memByte]
  simp only [PhysicalMemory.read]
  rw [maskMemN_getElem?_self h128 m a src mask i hi]
  split
  · rfl
  · rw [← hl, ← storedByte_extractLsb', storedByte_memLoad m a i (by omega)]
    rfl

/-! ### After a masked-store step -/

/-- A masked-store form's state from `t`: `Next_IP` set to `ip`, the oracle advanced by `f` (the
writability checks), then the masked stores of `src`'s bytes at `a`. -/
def maskStateN {n : Nat} (a : BitVec 64) (src mask : BitVec n) (ip : BitVec 64)
    (f : X86.Runtime.Oracle → X86.Runtime.Oracle) (t : RamState) : RamState :=
  maskStoresN a src mask { t with Next_IP := ip, oracle := f t.oracle }

/-- After a step ending in `maskStateN … ip f`, RIP is `ip`. -/
theorem afterStep_maskStateN_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n : Nat} (a : BitVec 64) (src mask : BitVec n) (ip : BitVec 64)
    (f : X86.Runtime.Oracle → X86.Runtime.Oracle) :
    (afterStep s length (maskStateN a src mask ip f)).RIP = ip := by
  simp [afterStep, finishStep, maskStateN, maskStoresN, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Memory after a masked-store step: the masked store. -/
@[simp] theorem afterStep_maskStateN_external (s : RamState) (length : Nat) {n : Nat}
    (a : BitVec 64) (src mask : BitVec n) (ip : BitVec 64)
    (f : X86.Runtime.Oracle → X86.Runtime.Oracle) :
    (afterStep s length (maskStateN a src mask ip f)).external = maskMemN s.external a src mask :=
  rfl

/-- After a masked-store step, the `n / 8` bytes at `a` read as the merged value. -/
theorem Operand.read_afterStep_maskStateN (s : RamState) (length : Nat) {n : Nat}
    (hn : n % 8 = 0) (h128 : n ≤ 128) (a : BitVec 64) (src mask : BitVec n) (ip : BitVec 64)
    (f : X86.Runtime.Oracle → X86.Runtime.Oracle) :
    (Operand.mem a : Operand n).read (afterStep s length (maskStateN a src mask ip f)) =
      maskMergeN src mask ((Operand.mem a : Operand n).read s) := by
  simp only [Operand.read, afterStep_maskStateN_external]
  exact memLoad_maskMemN hn h128 _ _ _ _

/-- Preservation for a masked store: if its `n / 8` bytes lie below 4 GiB and outside the
page-table frames, the state after the step is ready to step again. -/
theorem ReadyToStep.afterStep_maskStateN [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (a : BitVec 64) (src mask : BitVec n) (ip : BitVec 64)
    (f : X86.Runtime.Oracle → X86.Runtime.Oracle)
    (hlow : a.toNat + n / 8 ≤ 2^32) (htables : PageTableEntriesApart a.toNat (n / 8)) :
    ReadyToStep (afterStep s length (maskStateN a src mask ip f)) := by
  have hst : SameControls s (afterStep s length (maskStateN a src mask ip f)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory (afterStep s length (maskStateN a src mask ip f)) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [afterStep_maskStateN_external]
    exact IdentityPageTableMemory.maskMemN h.memory.tables _ _ _ hlow htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- A masked-store step changes only the `n / 8` bytes at `a` and RIP (besides the per-step
bookkeeping). -/
theorem AgreesExcept.afterStep_maskStateN (s : RamState) (length : Nat) {n : Nat} (a : BitVec 64)
    (src mask : BitVec n) (ip : BitVec 64) (f : X86.Runtime.Oracle → X86.Runtime.Oracle) :
    AgreesExcept [.mem a (n / 8), .rip] s (afterStep s length (maskStateN a src mask ip f)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · rw [afterStep_maskStateN_external]
    exact maskMemN_getElem?_of_ne _ _ _ _ _ fun i hi he =>
      hx (.mem a (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, afterStep, finishStep, maskStateN, maskStoresN, afterFetches,
      beforeFetch, resetStepFields]
  · rw [afterStep_maskStateN_external]
    exact maskMemN_isSome _ _ _ _ x hx

/-- The effect of a masked-store step from `s`, as a `Holds` fact. -/
theorem maskStateN_holds [Bindings] {s : RamState} (h : ReadyToStep s) {p : BitVec 64}
    {len n : Nat} (hn : n % 8 = 0) (h128 : n ≤ 128) (addr : RamState → BitVec 64)
    (src mask : RamState → BitVec n) (f : X86.Runtime.Oracle → X86.Runtime.Oracle) :
    (storeEffect p len addr (fun s => maskMergeN (src s) (mask s)
        ((Operand.mem (addr s) : Operand n).read s)) s).Holds s
      (afterStep s len (maskStateN (addr s) (src s) (mask s) (BitVec.add p (BitVec.ofNat 64 len))
        f)) :=
  ⟨afterStep_maskStateN_rip h _ _ _ _ _ _,
    Operand.read_afterStep_maskStateN s _ hn h128 _ _ _ _ _, trivial,
    by rw [storeEffect_components]
       exact AgreesExcept.afterStep_maskStateN s len (addr s) (src s) (mask s) _ f⟩

/--
The step of a masked store at `p` with its effect, under a precondition `P` that implies
`StorePre` for its `n / 8` bytes at `addr s`, from its step theorem: if from every ready state
with the instruction `bytes` at `p` and `P`, one `step` ends in
`maskStateN (addr s) (src s) (mask s) (p + len) f`, then that step has the effect
`storeEffect p len addr` of the merged bytes (`maskMergeN`, the old bytes read from the start
state).
-/
theorem StepEffect.of_maskStateN [Bindings] {P : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len n : Nat} (hn : n % 8 = 0) (h128 : n ≤ 128)
    (addr : RamState → BitVec 64) (src mask : RamState → BitVec n)
    (f : X86.Runtime.Oracle → X86.Runtime.Oracle)
    (hpre : ∀ s, P s → StorePre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len
        (maskStateN (addr s) (src s) (mask s) (BitVec.add p (BitVec.ofNat 64 len)) f)))) :
    StepEffect P (codeRange p bytes) (storeEffect p len addr fun s =>
      maskMergeN (src s) (mask s) ((Operand.mem (addr s) : Operand n).read s)) := by
  intro s h hcode hs
  have hp := hpre s hs
  exact ⟨_, hstep s h hcode hs,
    ReadyToStep.afterStep_maskStateN h _ _ _ _ _ _ hp.write.low hp.write.tables,
    maskStateN_holds h hn h128 addr src mask f⟩

/-- Entering MMX mode (`mmxEnter`) before a masked store is entering it after the step. -/
theorem afterStep_maskStateN_mmxEnter (s : RamState) (length : Nat) {n : Nat} (a : BitVec 64)
    (src mask : BitVec n) (ip : BitVec 64) (f : X86.Runtime.Oracle → X86.Runtime.Oracle) :
    (afterStep s length fun t => maskStateN a src mask ip f (mmxEnter t)) =
      mmxEnter (afterStep s length (maskStateN a src mask ip f)) := by
  simp only [afterStep, finishStep, maskStateN, maskStoresN, mmxEnter]
  rfl

/-- `StepEffect.of_maskStateN` for a form that enters MMX mode first (MASKMOVQ: TOP := 0, the tag
word := 0, `mmxEnter`): the effect is the store's with `Effect.withMmx`. -/
theorem StepEffect.of_maskStateN_mmx [Bindings] {P : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len n : Nat} (hn : n % 8 = 0) (h128 : n ≤ 128)
    (addr : RamState → BitVec 64) (src mask : RamState → BitVec n)
    (f : X86.Runtime.Oracle → X86.Runtime.Oracle)
    (hpre : ∀ s, P s → StorePre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        maskStateN (addr s) (src s) (mask s) (BitVec.add p (BitVec.ofNat 64 len)) f
          (mmxEnter t)))) :
    StepEffect P (codeRange p bytes) (fun s => (storeEffect p len addr (fun s =>
      maskMergeN (src s) (mask s) ((Operand.mem (addr s) : Operand n).read s)) s).withMmx s) := by
  intro s h hcode hs
  have hp := hpre s hs
  have hst := hstep s h hcode hs
  rw [afterStep_maskStateN_mmxEnter] at hst
  exact ⟨_, hst,
    (ReadyToStep.afterStep_maskStateN h _ _ _ _ _ _ hp.write.low hp.write.tables).of_mmxEnter,
    (maskStateN_holds h hn h128 addr src mask f).withMmx (by simp) (by simp)⟩

/-! ### MASKMOVDQU: 16 bytes -/

/-- Byte `i` of a 128-bit value is selected by `mask`: bit 7 of byte `i` of `mask` is set. -/
abbrev maskBit (mask : BitVec 128) (i : Nat) : Bool := maskBitN mask i

/-- The memory step of byte `i`: byte `i` of `src` stored at `a + i` if `mask` selects it. -/
abbrev maskMemByte (a : BitVec 64) (src mask : BitVec 128) (m : Ram) (i : Nat) : Ram :=
  maskMemByteN a src mask m i

/-- Memory `m` after the bytes of `src` that `mask` selects are stored at `a`, `a + 1`, …,
`a + 15`, one byte at a time from byte 0 up. -/
abbrev maskMem (m : Ram) (a : BitVec 64) (src mask : BitVec 128) : Ram :=
  maskMemN m a src mask

/-- The state after the write of byte `i` (if `mask` selects it), as lean-x86's loop body leaves
it: a one-byte data write at `a + i` with its bookkeeping (`dataAccess t "store"`), or nothing. -/
abbrev maskByteStore (a : BitVec 64) (src mask : BitVec 128) (i : Nat) (t : RamState) :
    RamState :=
  maskByteStoreN a src mask i t

/-- The oracle step of byte `i`: the 464 bits of a data write if `mask` selects it. -/
abbrev maskOracleByte (mask : BitVec 128) (o : X86.Runtime.Oracle) (i : Nat) :
    X86.Runtime.Oracle :=
  maskOracleByteN mask o i

/-- The trace step of byte `i`: a `store` event if `mask` selects it. -/
abbrev maskTraceByte (mask : BitVec 128) (r : List (String × String)) (i : Nat) :
    List (String × String) :=
  maskTraceByteN mask r i

/-- The state after the 16 byte writes of a masked store from `t`, in closed form: memory is
`maskMem`, and the oracle and the trace advance once per selected byte; nothing else changes. -/
abbrev maskStores (a : BitVec 64) (src mask : BitVec 128) (t : RamState) : RamState :=
  maskStoresN a src mask t

theorem foldl_maskByteStore (a : BitVec 64) (src mask : BitVec 128) (l : List Nat)
    (t : RamState) :
    l.foldl (fun u i => maskByteStore a src mask i u) t =
      { t with
        external := l.foldl (maskMemByte a src mask) t.external
        oracle := l.foldl (maskOracleByte mask) t.oracle
        traceEventsRev := l.foldl (maskTraceByte mask) t.traceEventsRev } :=
  foldl_maskByteStoreN a src mask l t

/-- The closed form is lean-x86's loop: the fold of `maskByteStore` over bytes 0 to 15. -/
theorem maskStores_eq_foldl (a : BitVec 64) (src mask : BitVec 128) (t : RamState) :
    (List.range 16).foldl (fun u i => maskByteStore a src mask i u) t = maskStores a src mask t :=
  maskStoresN_eq_foldl a src mask t

theorem foldl_maskMemByte_of_ne (a : BitVec 64) (src mask : BitVec 128) (l : List Nat) (m : Ram)
    (x : BitVec 64) (hx : ∀ i ∈ l, a + BitVec.ofNat 64 i ≠ x) :
    (l.foldl (maskMemByte a src mask) m)[x]? = m[x]? :=
  foldl_maskMemByteN_of_ne a src mask l m x hx

/-- A byte outside the 16 bytes at `a` is unchanged by a masked store. -/
theorem maskMem_getElem?_of_ne (m : Ram) (a : BitVec 64) (src mask : BitVec 128) (x : BitVec 64)
    (hx : ∀ i < 16, a + BitVec.ofNat 64 i ≠ x) : (maskMem m a src mask)[x]? = m[x]? :=
  maskMemN_getElem?_of_ne m a src mask x hx

theorem foldl_maskMemByte_self (a : BitVec 64) (src mask : BitVec 128) (l : List Nat) (m : Ram)
    (j : Nat) (hj : j < 16) (hl : ∀ i ∈ l, i < 16) :
    (l.foldl (maskMemByte a src mask) m)[a + BitVec.ofNat 64 j]? =
      if j ∈ l ∧ maskBit mask j = true then some (storedByte (lane 8 src j) 0)
      else m[a + BitVec.ofNat 64 j]? :=
  foldl_maskMemByteN_self (by decide) a src mask l m j hj hl

/-- Byte `j` (`j < 16`) of a masked store at `a`: byte `j` of `src` if `mask` selects it, else the
old byte. -/
theorem maskMem_getElem?_self (m : Ram) (a : BitVec 64) (src mask : BitVec 128) (j : Nat)
    (hj : j < 16) :
    (maskMem m a src mask)[a + BitVec.ofNat 64 j]? =
      if maskBit mask j then some (storedByte (lane 8 src j) 0)
      else m[a + BitVec.ofNat 64 j]? :=
  maskMemN_getElem?_self (by decide) m a src mask j hj

/-- A masked store keeps every byte of RAM present. -/
theorem maskMem_isSome (m : Ram) (a : BitVec 64) (src mask : BitVec 128) (x : BitVec 64)
    (h : (m[x]?).isSome) : ((maskMem m a src mask)[x]?).isSome :=
  maskMemN_isSome m a src mask x h

/-- A masked store keeps the identity-mapped page tables if its 16 bytes lie below 4 GiB and
outside the page-table frames. -/
theorem IdentityPageTableMemory.maskMem {m : Ram} (h : IdentityPageTableMemory m) (a : BitVec 64)
    (src mask : BitVec 128) (hlow : a.toNat + 16 ≤ 2^32)
    (htables : PageTableEntriesApart a.toNat 16) :
    IdentityPageTableMemory (X86Proofs.maskMem m a src mask) :=
  h.maskMemN a src mask hlow htables

/-- The 16 bytes at `a` after a masked store, read back: lane `i` is lane `i` of `src` if `mask`
selects it, else the old lane. -/
theorem memLoad_maskMem (m : Ram) (a : BitVec 64) (src mask : BitVec 128) :
    memLoad (maskMem m a src mask) a 128 =
      ofLanes 128 8 fun i =>
        if maskBit mask i then lane 8 src i else lane 8 (memLoad m a 128) i :=
  memLoad_maskMemN (by decide) (by decide) m a src mask

/-- MASKMOVDQU's state after its form from `t`: `Next_IP` set to `ip`, the oracle bits of the two
writability checks (of bytes 0–7 and 8–15), then the masked stores of `src`'s bytes at `a`. -/
abbrev maskmovState (a : BitVec 64) (src mask : BitVec 128) (ip : BitVec 64) (t : RamState) :
    RamState :=
  maskStateN a src mask ip (fun o => oracleSkip (oracleSkip o 464) 464) t

/-- The merged 16 bytes a masked store leaves at its address: lane `i` of `src` where `mask`
selects it, else lane `i` of the old value `old`. -/
abbrev maskMerge (src mask old : BitVec 128) : BitVec 128 := maskMergeN src mask old

/-- After a step ending in `maskmovState … ip`, RIP is `ip`. -/
theorem afterStep_maskmov_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (a : BitVec 64) (src mask : BitVec 128) (ip : BitVec 64) :
    (afterStep s length (maskmovState a src mask ip)).RIP = ip :=
  afterStep_maskStateN_rip h length a src mask ip _

/-- Memory after MASKMOVDQU's step: the masked store. -/
@[simp] theorem afterStep_maskmov_external (s : RamState) (length : Nat) (a : BitVec 64)
    (src mask : BitVec 128) (ip : BitVec 64) :
    (afterStep s length (maskmovState a src mask ip)).external = maskMem s.external a src mask :=
  rfl

/-- After MASKMOVDQU's step, the 16 bytes at `a` read as the merged value. -/
theorem Operand.read_afterStep_maskmov (s : RamState) (length : Nat) (a : BitVec 64)
    (src mask : BitVec 128) (ip : BitVec 64) :
    (Operand.mem a : Operand 128).read (afterStep s length (maskmovState a src mask ip)) =
      maskMerge src mask ((Operand.mem a : Operand 128).read s) :=
  Operand.read_afterStep_maskStateN s length (by decide) (by decide) a src mask ip _

/-- Preservation for MASKMOVDQU: if its 16 bytes lie below 4 GiB and outside the page-table
frames, the state after the step is ready to step again. -/
theorem ReadyToStep.afterStep_maskmov [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (a : BitVec 64) (src mask : BitVec 128) (ip : BitVec 64)
    (hlow : a.toNat + 16 ≤ 2^32) (htables : PageTableEntriesApart a.toNat 16) :
    ReadyToStep (afterStep s length (maskmovState a src mask ip)) :=
  h.afterStep_maskStateN length a src mask ip _ hlow htables

/-- MASKMOVDQU's step changes only the 16 bytes at `a` and RIP (besides the per-step
bookkeeping). -/
theorem AgreesExcept.afterStep_maskmov (s : RamState) (length : Nat) (a : BitVec 64)
    (src mask : BitVec 128) (ip : BitVec 64) :
    AgreesExcept [.mem a 16, .rip] s (afterStep s length (maskmovState a src mask ip)) :=
  AgreesExcept.afterStep_maskStateN s length a src mask ip _

/--
The step of MASKMOVDQU at `p` with its effect, under a precondition `P` that implies `StorePre`
for its 16 bytes at `addr s`, from its step theorem: if from every ready state with the
instruction `bytes` at `p` and `P`, one `step` ends in `maskmovState (addr s) (src s) (mask s)`
with `Next_IP` = `p + len`, then that step has the effect `storeEffect p len addr` of the merged 16
bytes (`maskMerge`, the old bytes read from the start state).
-/
theorem StepEffect.of_maskmov [Bindings] {P : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} (addr : RamState → BitVec 64)
    (src mask : RamState → BitVec 128)
    (hpre : ∀ s, P s → StorePre p len addr 16 s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len
        (maskmovState (addr s) (src s) (mask s) (BitVec.add p (BitVec.ofNat 64 len)))))) :
    StepEffect P (codeRange p bytes) (storeEffect p len addr fun s =>
      maskMerge (src s) (mask s) ((Operand.mem (addr s) : Operand 128).read s)) :=
  StepEffect.of_maskStateN (by decide) (by decide) addr src mask _ hpre hstep

/-! ### MASKMOVQ: 8 bytes, MMX mode -/

/-- MASKMOVQ's state after its form from `t`: TOP := 0 and the tag word := 0 (`mmxEnter`),
`Next_IP` set to `ip`, the oracle bits of the one writability check (of the 8 bytes), then the
masked stores of `src`'s bytes at `a`. -/
abbrev maskmovqState (a : BitVec 64) (src mask : BitVec 64) (ip : BitVec 64) (t : RamState) :
    RamState :=
  maskStateN a src mask ip (fun o => oracleSkip o 464) (mmxEnter t)

end X86Proofs
