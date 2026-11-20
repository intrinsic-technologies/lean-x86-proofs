import X86Proofs.Program.ReadWrite.Sse
import X86Proofs.Program.ReadWrite.String
import X86Proofs.Core.Float

/-!
# Floating-point SSE writes: an XMM register and MXCSR

A floating-point SSE form with an XMM destination (ADDSS, MULPD, SQRTSD, …) ends, after its
operation has ORed the exception flags into MXCSR (`FP.Check_Exceptions`, `Core/Float.lean`), in
`writeResult (mxcsr.write t m) (.xmm r) v nextIP` (register source) or
`writeResult (mxcsr.write (dataAccess t "load") m) (.xmm r) v nextIP` (memory source), `mxcsr` the
32-bit operand `Operand.mxcsr`. After such a step:

- `afterStep_writeResult_xmm_mxcsr_rip`, `afterStep_load_xmm_mxcsr_rip`: RIP is `nextIP`;
- `Operand.read_afterStep_writeResult_xmm_mxcsr`, `Operand.read_afterStep_load_xmm_mxcsr` (the
  register reads `v`), `Operand.read_afterStep_writeResult_mxcsr`,
  `Operand.read_afterStep_load_mxcsr` (MXCSR reads `m`);
- `ReadyToStep.afterStep_writeResult_xmm_mxcsr`, `ReadyToStep.afterStep_load_xmm_mxcsr`: the state
  is ready to step again;
- `AgreesExcept.afterStep_writeResult_xmm_mxcsr`, `AgreesExcept.afterStep_load_xmm_mxcsr`: only
  that XMM register (its low 128 bits), MXCSR and RIP change.

A conversion to an integer in a general-purpose register (CVTSS2SI, CVTTSD2SI, …) ends in
`writeResult (mxcsr.write t m) (.reg r : Operand n) v nextIP` (or with `dataAccess t "load"`):
`AgreesExcept.afterStep_writeResult_reg_mxcsr`, `AgreesExcept.afterStep_load_reg_mxcsr` (only
that register, MXCSR and RIP change), `afterStep_writeResult_reg_mxcsr_rip`,
`afterStep_load_reg_mxcsr_rip`, `ReadyToStep.afterStep_writeResult_reg_mxcsr`,
`ReadyToStep.afterStep_load_reg_mxcsr`; the register and MXCSR read back through
`Operand.read_afterStep`.

A floating-point comparison into the status flags (COMISS, UCOMISS) ends in
`writeFpFlags t m f nextIP` (`Next_IP`, MXCSR `m`, the flags `f`) or
`writeFpFlags (dataAccess t "load") m f nextIP`: `AgreesExcept.afterStep_writeFpFlags` (only MXCSR,
the flags and RIP change), the RIP, MXCSR and flags read-backs (`afterStep_writeFpFlags_rip`,
`Operand.read_afterStep_writeFpFlags_mxcsr`, `ofRFLAGS_afterStep_writeFpFlags`) and
`ReadyToStep.afterStep_writeFpFlags`, each with its `load` version.

LDMXCSR ends in `writeResult (dataAccess t "load") (.mxcsr) v nextIP`:
`AgreesExcept.afterStep_ldmxcsr` (only MXCSR and RIP change), `Operand.read_afterStep_ldmxcsr`,
`ReadyToStep.afterStep_ldmxcsr` (RIP: the general `afterStep_load_rip`); its precondition is
`LdmxcsrPre p addr` (`SseLoadNPre` of the 4 bytes, the reserved bits 16–31 of the doubleword clear).

`FpPre pre ok s`: the precondition of a floating-point triple: `pre` (the precondition of the same
form without floating point: RIP, SSE enabled, a load's bytes readable, …), the exception masks set
(`MxcsrPre`), and `ok`, that lean-x86's float function returns a value on the operands (`FpArithOk`,
…, through the operation's `<op>Ok`). `NumPre pre ok s` is the same without the masks, for the
forms that neither read nor write MXCSR (RCPSS, RCPPS, RSQRTSS, RSQRTPS).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The precondition of a floating-point SSE triple: `pre s` (RIP, SSE enabled, the memory
operand's bytes, …), every SIMD floating-point exception masked (`MxcsrPre`), and `ok s`, that
lean-x86's float function returns a value on the operands the instruction reads in `s`. -/
structure FpPre (pre ok : RamState → Prop) (s : RamState) : Prop where
  pre : pre s
  mxcsr : MxcsrPre s
  ok : ok s

/-- The precondition of an SSE triple whose result lean-x86 computes with a numerical binding and
without MXCSR (RCPSS, RSQRTPS, …): `pre s` (RIP, SSE enabled, the memory operand's bytes, …) and
`ok s`, that lean-x86's function returns a value on the operands the instruction reads in `s`. -/
structure NumPre (pre ok : RamState → Prop) (s : RamState) : Prop where
  pre : pre s
  ok : ok s

@[simp] theorem afterFetches_MXCSR (s : RamState) (k : Nat) : (afterFetches s k).MXCSR = s.MXCSR :=
  rfl

@[simp] theorem beforeFetch_MXCSR (s : RamState) : (beforeFetch s).MXCSR = s.MXCSR := rfl

@[simp] theorem dataAccess_MXCSR (s : RamState) (event : String) :
    (dataAccess s event).MXCSR = s.MXCSR := rfl

/-- An MXCSR write changes only MXCSR. -/
theorem AgreesExcept.write_mxcsr (t : RamState) (m : BitVec 32) :
    AgreesExcept [.mxcsr] t ((Operand.mxcsr : Operand 32).write t m) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | mxcsr => exact absurd List.mem_cons_self hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · simp only [fixedPart, Operand.write_mxcsr, beforeFetch, resetStepFields]

theorem components_xmm_mxcsr_rip (r : BitVec 5) :
    ∀ c ∈ ([] ++ [.mxcsr] ++ [.xmm r] ++ [.rip] : List Component), c ∈ [.xmm r, .mxcsr, .rip] := by
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hc ⊢
  rcases hc with h | h | h <;> simp [h]

/-- A step whose form ends in `writeResult` to XMM register `r` after MXCSR is set to `m` changes
only `r` (its low 128 bits), MXCSR and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_writeResult_xmm_mxcsr (s : RamState) (length : Nat)
    (r : BitVec 5) (v : RamState → BitVec 128) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    AgreesExcept [.xmm r, .mxcsr, .rip] s
      (afterStep s length fun t =>
        writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.xmm r) (v t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { t with Next_IP := nextIP }
  have h1 := AgreesExcept.prepare s (length + 1) nextIP
  have h2 := AgreesExcept.write_mxcsr t0 (m t)
  have h3 := AgreesExcept.write_xmm ((Operand.mxcsr : Operand 32).write t0 (m t)) r (v t)
  have h4 := AgreesExcept.of_finishStep
    ((Operand.xmm r : Operand 128).write ((Operand.mxcsr : Operand 32).write t0 (m t)) (v t))
  exact (((h1.trans h2).trans h3).trans h4).mono (components_xmm_mxcsr_rip r)

/-- A load into XMM register `r` after which MXCSR is set to `m` changes only `r` (its low 128
bits), MXCSR and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_load_xmm_mxcsr (s : RamState) (length : Nat) (r : BitVec 5)
    (v : RamState → BitVec 128) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    AgreesExcept [.xmm r, .mxcsr, .rip] s
      (afterStep s length fun t =>
        writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.xmm r)
          (v t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { dataAccess t "load" with Next_IP := nextIP }
  have h1 : AgreesExcept [] s t0 := by
    refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | mem a l => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | _ => rfl
    · simp only [t0, t, fixedPart, dataAccess, afterFetches, beforeFetch, resetStepFields]
  have h2 := AgreesExcept.write_mxcsr t0 (m t)
  have h3 := AgreesExcept.write_xmm ((Operand.mxcsr : Operand 32).write t0 (m t)) r (v t)
  have h4 := AgreesExcept.of_finishStep
    ((Operand.xmm r : Operand 128).write ((Operand.mxcsr : Operand 32).write t0 (m t)) (v t))
  exact (((h1.trans h2).trans h3).trans h4).mono (components_xmm_mxcsr_rip r)

/-- After a step whose form ends in `writeResult … nextIP` after an MXCSR write, RIP is
`nextIP`. -/
theorem afterStep_writeResult_xmm_mxcsr_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 5) (v : RamState → BitVec 128) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.xmm r) (v t) nextIP).RIP =
      nextIP := by
  simp [afterStep, finishStep, writeResult, Operand.write, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem afterStep_load_xmm_mxcsr_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 5) (v : RamState → BitVec 128) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.xmm r) (v t)
        nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeResult, Operand.write, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After the step, XMM register `r` reads the value written. -/
theorem Operand.read_afterStep_writeResult_xmm_mxcsr (s : RamState) (length : Nat) (r : BitVec 5)
    (v : RamState → BitVec 128) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    (Operand.xmm r : Operand 128).read
        (afterStep s length fun t =>
          writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.xmm r) (v t) nextIP) =
      v (afterFetches (beforeFetch s) (length + 1)) := by
  rw [Operand.read_afterStep]
  exact Operand.read_write_xmm_self _ _ _

theorem Operand.read_afterStep_load_xmm_mxcsr (s : RamState) (length : Nat) (r : BitVec 5)
    (v : RamState → BitVec 128) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    (Operand.xmm r : Operand 128).read
        (afterStep s length fun t =>
          writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.xmm r)
            (v t) nextIP) =
      v (afterFetches (beforeFetch s) (length + 1)) := by
  rw [Operand.read_afterStep]
  exact Operand.read_write_xmm_self _ _ _

/-- After the step, MXCSR reads the value written. -/
theorem Operand.read_afterStep_writeResult_mxcsr (s : RamState) (length : Nat) (r : BitVec 5)
    (v : RamState → BitVec 128) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    (Operand.mxcsr : Operand 32).read
        (afterStep s length fun t =>
          writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.xmm r) (v t) nextIP) =
      m (afterFetches (beforeFetch s) (length + 1)) := rfl

theorem Operand.read_afterStep_load_mxcsr (s : RamState) (length : Nat) (r : BitVec 5)
    (v : RamState → BitVec 128) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    (Operand.mxcsr : Operand 32).read
        (afterStep s length fun t =>
          writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.xmm r)
            (v t) nextIP) =
      m (afterFetches (beforeFetch s) (length + 1)) := rfl

/-- Preservation for a form ending in `writeResult` to an XMM register after an MXCSR write. -/
theorem ReadyToStep.afterStep_writeResult_xmm_mxcsr [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 5) (v : RamState → BitVec 128) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.xmm r) (v t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.xmm r) (v t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

theorem ReadyToStep.afterStep_load_xmm_mxcsr [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 5) (v : RamState → BitVec 128) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.xmm r) (v t)
        nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.xmm r) (v t)
        nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-! ### A general-purpose register and MXCSR: CVTSS2SI, … -/

/-- The frame of a register write after an MXCSR write, in `[.reg r, .mxcsr, .rip]`. -/
theorem components_reg_mxcsr_rip (r : BitVec 5) :
    ∀ c ∈ ([] ++ [.mxcsr] ++ [.reg r] ++ [.rip] : List Component), c ∈ [.reg r, .mxcsr, .rip] := by
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hc ⊢
  rcases hc with h | h | h <;> simp [h]

/-- A step whose form ends in `writeResult` to register `r` (`n` bits) after MXCSR is set to `m`
changes only `r`, MXCSR and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_writeResult_reg_mxcsr (s : RamState) (length : Nat) {n : Nat}
    (r : BitVec 5) (v : RamState → BitVec n) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    AgreesExcept [.reg r, .mxcsr, .rip] s
      (afterStep s length fun t =>
        writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.reg r) (v t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { t with Next_IP := nextIP }
  have h1 := AgreesExcept.prepare s (length + 1) nextIP
  have h2 := AgreesExcept.write_mxcsr t0 (m t)
  have h3 := AgreesExcept.write_reg ((Operand.mxcsr : Operand 32).write t0 (m t)) r (v t)
  have h4 := AgreesExcept.of_finishStep
    ((Operand.reg r : Operand n).write ((Operand.mxcsr : Operand 32).write t0 (m t)) (v t))
  exact (((h1.trans h2).trans h3).trans h4).mono (components_reg_mxcsr_rip r)

/-- The same with a memory source (`dataAccess t "load"` first). -/
theorem AgreesExcept.afterStep_load_reg_mxcsr (s : RamState) (length : Nat) {n : Nat}
    (r : BitVec 5) (v : RamState → BitVec n) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    AgreesExcept [.reg r, .mxcsr, .rip] s
      (afterStep s length fun t =>
        writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.reg r)
          (v t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { dataAccess t "load" with Next_IP := nextIP }
  have h1 : AgreesExcept [] s t0 := by
    refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | mem a l => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | _ => rfl
    · simp only [t0, t, fixedPart, dataAccess, afterFetches, beforeFetch, resetStepFields]
  have h2 := AgreesExcept.write_mxcsr t0 (m t)
  have h3 := AgreesExcept.write_reg ((Operand.mxcsr : Operand 32).write t0 (m t)) r (v t)
  have h4 := AgreesExcept.of_finishStep
    ((Operand.reg r : Operand n).write ((Operand.mxcsr : Operand 32).write t0 (m t)) (v t))
  exact (((h1.trans h2).trans h3).trans h4).mono (components_reg_mxcsr_rip r)

/-- After a step whose form ends in `writeResult … nextIP` to a register after an MXCSR write,
RIP is `nextIP`. -/
theorem afterStep_writeResult_reg_mxcsr_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r : BitVec 5) (v : RamState → BitVec n) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.reg r) (v t) nextIP).RIP =
      nextIP := by
  simp [afterStep, finishStep, writeResult, Operand.write, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- The same with a memory source. -/
theorem afterStep_load_reg_mxcsr_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r : BitVec 5) (v : RamState → BitVec n) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.reg r) (v t)
        nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeResult, Operand.write, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Preservation for a form ending in `writeResult` to a register after an MXCSR write. -/
theorem ReadyToStep.afterStep_writeResult_reg_mxcsr [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r : BitVec 5) (v : RamState → BitVec n) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.reg r) (v t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.reg r) (v t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- The same with a memory source. -/
theorem ReadyToStep.afterStep_load_reg_mxcsr [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r : BitVec 5) (v : RamState → BitVec n) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.reg r) (v t)
        nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.reg r) (v t)
        nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-! ### Flags and MXCSR: COMISS, UCOMISS, … -/

/-- The form-level result of a floating-point comparison into the status flags (COMISS, UCOMISS):
`t` with `Next_IP` set, MXCSR set to `m` (the exception flags ORed in) and the status flags `f`
stored. -/
def writeFpFlags (t : RamState) (m : BitVec 32) (f : StatusFlags) (nextIP : BitVec 64) :
    RamState :=
  setFlags { t with Next_IP := nextIP, MXCSR := m } f

theorem components_mxcsr_flags_rip :
    ∀ c ∈ ([] ++ [.mxcsr] ++ [.flags] ++ [.rip] : List Component),
      c ∈ [.mxcsr, .flags, .rip] := by
  intro c hc
  simpa using hc

/-- Storing status flags changes only the flags. -/
theorem AgreesExcept.setFlags (t : RamState) (f : StatusFlags) :
    AgreesExcept [.flags] t (X86Proofs.setFlags t f) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | flags => exact absurd List.mem_cons_self hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | df => exact dfBit_store _ _
    | _ => rfl
  · simp only [fixedPart, X86Proofs.setFlags, beforeFetch, resetStepFields, clearStatusFlags_store]

/-- A step whose form ends in `writeFpFlags` (register operands) changes only MXCSR, the status
flags and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_writeFpFlags (s : RamState) (length : Nat)
    (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    AgreesExcept [.mxcsr, .flags, .rip] s
      (afterStep s length fun t => writeFpFlags t (m t) (f t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { t with Next_IP := nextIP }
  have h1 := AgreesExcept.prepare s (length + 1) nextIP
  have h2 := AgreesExcept.write_mxcsr t0 (m t)
  have h3 := AgreesExcept.setFlags ((Operand.mxcsr : Operand 32).write t0 (m t)) (f t)
  have h4 := AgreesExcept.of_finishStep
    (X86Proofs.setFlags ((Operand.mxcsr : Operand 32).write t0 (m t)) (f t))
  exact (((h1.trans h2).trans h3).trans h4).mono components_mxcsr_flags_rip

/-- The same with a memory operand (`dataAccess t "load"` first). -/
theorem AgreesExcept.afterStep_load_writeFpFlags (s : RamState) (length : Nat)
    (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    AgreesExcept [.mxcsr, .flags, .rip] s
      (afterStep s length fun t => writeFpFlags (dataAccess t "load") (m t) (f t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { dataAccess t "load" with Next_IP := nextIP }
  have h1 : AgreesExcept [] s t0 := by
    refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | mem a l => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | _ => rfl
    · simp only [t0, t, fixedPart, dataAccess, afterFetches, beforeFetch, resetStepFields]
  have h2 := AgreesExcept.write_mxcsr t0 (m t)
  have h3 := AgreesExcept.setFlags ((Operand.mxcsr : Operand 32).write t0 (m t)) (f t)
  have h4 := AgreesExcept.of_finishStep
    (X86Proofs.setFlags ((Operand.mxcsr : Operand 32).write t0 (m t)) (f t))
  exact (((h1.trans h2).trans h3).trans h4).mono components_mxcsr_flags_rip

theorem afterStep_writeFpFlags_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeFpFlags t (m t) (f t) nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeFpFlags, X86Proofs.setFlags, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem afterStep_load_writeFpFlags_rip [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeFpFlags (dataAccess t "load") (m t) (f t) nextIP).RIP =
      nextIP := by
  simp [afterStep, finishStep, writeFpFlags, X86Proofs.setFlags, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After the step, MXCSR reads the value written. -/
theorem Operand.read_afterStep_writeFpFlags_mxcsr (s : RamState) (length : Nat)
    (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    (Operand.mxcsr : Operand 32).read
        (afterStep s length fun t => writeFpFlags t (m t) (f t) nextIP) =
      m (afterFetches (beforeFetch s) (length + 1)) := by
  simp [Operand.read, afterStep, finishStep, writeFpFlags, X86Proofs.setFlags]

theorem Operand.read_afterStep_load_writeFpFlags_mxcsr (s : RamState) (length : Nat)
    (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    (Operand.mxcsr : Operand 32).read
        (afterStep s length fun t => writeFpFlags (dataAccess t "load") (m t) (f t) nextIP) =
      m (afterFetches (beforeFetch s) (length + 1)) := by
  simp [Operand.read, afterStep, finishStep, writeFpFlags, X86Proofs.setFlags]

/-- After the step, the status flags are those stored. -/
theorem ofRFLAGS_afterStep_writeFpFlags (s : RamState) (length : Nat)
    (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    StatusFlags.ofRFLAGS (afterStep s length fun t => writeFpFlags t (m t) (f t) nextIP).RFLAGS =
      f (afterFetches (beforeFetch s) (length + 1)) := by
  simp [afterStep, finishStep, writeFpFlags, X86Proofs.setFlags, StatusFlags.ofRFLAGS_store]

theorem ofRFLAGS_afterStep_load_writeFpFlags (s : RamState) (length : Nat)
    (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    StatusFlags.ofRFLAGS (afterStep s length fun t =>
      writeFpFlags (dataAccess t "load") (m t) (f t) nextIP).RFLAGS =
      f (afterFetches (beforeFetch s) (length + 1)) := by
  simp [afterStep, finishStep, writeFpFlags, X86Proofs.setFlags, StatusFlags.ofRFLAGS_store]

/-- Preservation for a form ending in `writeFpFlags`. -/
theorem ReadyToStep.afterStep_writeFpFlags [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeFpFlags t (m t) (f t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t => writeFpFlags t (m t) (f t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf,
      StatusFlags.resumeFlagClear_store _ hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

theorem ReadyToStep.afterStep_load_writeFpFlags [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (m : RamState → BitVec 32) (f : RamState → StatusFlags) (nextIP : BitVec 64) :
    ReadyToStep
      (afterStep s length fun t => writeFpFlags (dataAccess t "load") (m t) (f t) nextIP) := by
  have hst : SameControls s
      (afterStep s length fun t => writeFpFlags (dataAccess t "load") (m t) (f t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf,
      StatusFlags.resumeFlagClear_store _ hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-! ### LDMXCSR: a load into MXCSR -/

/-- The precondition of an LDMXCSR triple at `p`: an SSE load of the 4 bytes at `addr s`
(`SseLoadNPre`), whose doubleword has the reserved MXCSR bits 16–31 clear (else #GP). -/
structure LdmxcsrPre [Bindings] (p : BitVec 64) (addr : RamState → BitVec 64) (s : RamState) :
    Prop extends SseLoadNPre p addr 4 s where
  reserved : ((Operand.mem (addr s) : Operand 32).read s).extractLsb' 16 16 = 0

/-- A load into MXCSR changes only MXCSR and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_ldmxcsr (s : RamState) (length : Nat) (v : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    AgreesExcept [.mxcsr, .rip] s
      (afterStep s length fun t =>
        writeResult (dataAccess t "load") (.mxcsr : Operand 32) (v t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { dataAccess t "load" with Next_IP := nextIP }
  have h1 : AgreesExcept [] s t0 := by
    refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | mem a l => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | _ => rfl
    · simp only [t0, t, fixedPart, dataAccess, afterFetches, beforeFetch, resetStepFields]
  have h2 := AgreesExcept.write_mxcsr t0 (v t)
  have h3 := AgreesExcept.of_finishStep ((Operand.mxcsr : Operand 32).write t0 (v t))
  exact ((h1.trans h2).trans h3).mono (by simp)

/-- After a load into MXCSR, MXCSR reads the value loaded. -/
theorem Operand.read_afterStep_ldmxcsr (s : RamState) (length : Nat) (v : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    (Operand.mxcsr : Operand 32).read
        (afterStep s length fun t =>
          writeResult (dataAccess t "load") (.mxcsr : Operand 32) (v t) nextIP) =
      v (afterFetches (beforeFetch s) (length + 1)) := by
  rw [Operand.read_afterStep]
  simp [writeResult]

/-- Preservation for a load into MXCSR. -/
theorem ReadyToStep.afterStep_ldmxcsr [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (v : RamState → BitVec 32) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (dataAccess t "load") (.mxcsr : Operand 32) (v t) nextIP) := by
  have hst : SameControls s (afterStep s length fun t =>
      writeResult (dataAccess t "load") (.mxcsr : Operand 32) (v t) nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      hc.debug, hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-! ### Preconditions after a block

The exception masks after a block (`MxcsrPre`: kept by every MXCSR write `mxOr` leaves, read off
the canonical state), and the carry-over lemmas of `FpPre`, `NumPre`, `LdmxcsrPre`. -/

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre_simp] theorem mxOr_extractLsb'_masks (m : BitVec 32) (f : BitVec 6) :
    (mxOr m f).extractLsb' 7 6 = m.extractLsb' 7 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mxOr, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_or]
  simp [BitVec.getLsbD_of_ge f (7 + i) (by omega)]

@[x86_pre_simp] theorem mxcsrPre_iff (t : RamState) :
    MxcsrPre t ↔ ((Operand.mxcsr : Operand 32).read t).extractLsb' 7 6 = 63#6 := by
  simp [MxcsrPre, Operand.read]

@[x86_pre] theorem MxcsrPre.of_holds (ho : Obs (e.after s true) s')
    (hm : ((Operand.mxcsr : Operand 32).read (e.after s true)).extractLsb' 7 6 = 63#6) :
    MxcsrPre s' := by
  rw [mxcsrPre_iff, Obs.back_mxcsr ho]
  exact hm

@[x86_pre] theorem LdmxcsrPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {addr : RamState → BitVec 64}
    (hrip : e.rip = p) (hsse : Prelude.SupportedSSE Bindings.processor s) (ha : AddrObs addr)
    (hr : MemReadable s (addr (e.after s true)) 4)
    (hres : ((Operand.mem (addr (e.after s true)) : Operand 32).read (e.after s true)).extractLsb'
      16 16 = 0) :
    LdmxcsrPre p addr s' :=
  ⟨SseLoadNPre.of_holds h ho hrip hsse ha hr,
    by rw [ha.eq ho, Obs.back_mem ho]; exact hres⟩

end Carry

end X86Proofs
