import X86Proofs.Step.ReadyToStep
import X86Proofs.Core.Operand

/-!
# Per-step housekeeping, and what a step preserves

`afterStep s length form` is the state `step s` ends in for an instruction of `length` bytes
decoded through `Decode_Legacy_0` whose form's code does `form`. It hides the housekeeping that
is the same for every such instruction: the bookkeeping reset at the start of the step, the oracle
bits the byte fetches use up, and RIP := `Next_IP` at the end. Step theorems state their result as
`afterStep s length (fun t => writeOutputs t …)`, where `fun t => writeOutputs t …` is the form
lemma's result on the state `t` the form starts from.

`ReadyToStep.afterStep_writeOutputs`: after a register-destination form, `ReadyToStep` still holds;
`ReadyToStep.afterStep_writeFlagsOutputs`: the same after a flags-only form (`writeFlagsOutputs`, CMP and TEST).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
The state `step s` ends in when the instruction at RIP is `length` bytes long, is decoded by
`Decode_Legacy_0` (any prefixes, then a one-byte opcode, then ModRM and further bytes), and its
form's code turns the state `t` it starts from into `form t`:

1. the per-step bookkeeping fields are reset (`beforeFetch`);
2. the fetches use up their oracle bits: one fetch per instruction byte, plus one because the
   prefix scan and the decoder both read the opcode byte;
3. the form runs;
4. RIP := `Next_IP` (`finishStep`).
-/
def afterStep (s : RamState) (length : Nat) (form : RamState → RamState) : RamState :=
  finishStep (form (afterFetches (beforeFetch s) (length + 1)))

/-! ### Frame facts: what the housekeeping leaves alone -/

@[simp] theorem afterFetches_external (s : RamState) (k : Nat) :
    (afterFetches s k).external = s.external := rfl

@[simp] theorem beforeFetch_external (s : RamState) : (beforeFetch s).external = s.external := rfl

@[simp] theorem finishStep_external (s : RamState) : (finishStep s).external = s.external := rfl

/-- The fetches leave RFLAGS alone (the flags an instruction reads, e.g. ADC's carry-in, are those
before the step). -/
@[simp] theorem afterFetches_RFLAGS (s : RamState) (k : Nat) : (afterFetches s k).RFLAGS = s.RFLAGS :=
  rfl

@[simp] theorem beforeFetch_RFLAGS (s : RamState) : (beforeFetch s).RFLAGS = s.RFLAGS := rfl

/-- Memory after a step is memory after its form; the housekeeping does not touch it. -/
theorem afterStep_external (s : RamState) (length : Nat) (form : RamState → RamState) :
    (afterStep s length form).external =
      (form (afterFetches (beforeFetch s) (length + 1))).external := rfl

@[simp] theorem Operand.read_afterFetches {n : Nat} (s : RamState) (k : Nat) (op : Operand n) :
    op.read (afterFetches s k) = op.read s :=
  Operand.read_of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl op

@[simp] theorem Operand.read_beforeFetch {n : Nat} (s : RamState) (op : Operand n) :
    op.read (beforeFetch s) = op.read s :=
  Operand.read_of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl op

/-- Operand reads after a step are operand reads after its form; the housekeeping does not
touch the general-purpose registers or memory. -/
theorem Operand.read_afterStep {n : Nat} (s : RamState) (length : Nat) (form : RamState → RamState)
    (op : Operand n) :
    op.read (afterStep s length form) = op.read (form (afterFetches (beforeFetch s) (length + 1))) :=
  Operand.read_of_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl op

/-- A step whose form ends in `writeOutputs` to a register leaves memory unchanged. -/
@[simp] theorem afterStep_writeOutputs_external (s : RamState) (length : Nat) {n : Nat} (r : BitVec 5)
    (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeOutputs t (.reg r) (out t) oracleUsed nextIP).external =
      s.external := rfl

/-- A step whose form ends in `writeFlagsOutputs` leaves memory unchanged. -/
@[simp] theorem afterStep_writeFlagsOutputs_external (s : RamState) (length : Nat)
    (f : RamState → StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeFlagsOutputs t (f t) oracleUsed nextIP).external = s.external := rfl

/-- Code bytes survive a step whose form ends in `writeOutputs` to a register. -/
theorem BytesAt.afterStep_writeOutputs {s : RamState} {addr : BitVec 64} {bytes : List UInt8}
    (h : BytesAt s addr bytes) (length : Nat) {n : Nat} (r : BitVec 5)
    (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    BytesAt (afterStep s length fun t => writeOutputs t (.reg r) (out t) oracleUsed nextIP) addr
      bytes :=
  BytesAt.of_external_eq rfl h

/-- Storing status flags keeps TF (bit 8) clear. -/
theorem StatusFlags.trapFlagClear_store (f : StatusFlags) {r : BitVec 64}
    (h : Prelude.RFLAGS.TrapFlagClear r) : Prelude.RFLAGS.TrapFlagClear (f.store r) :=
  ⟨(StatusFlags.extractLsb'_store f r 8 (by decide)).trans h.tf⟩

/-- Storing status flags keeps RF (bit 16) clear. -/
theorem StatusFlags.resumeFlagClear_store (f : StatusFlags) {r : BitVec 64}
    (h : Prelude.RFLAGS.ResumeFlagClear r) : Prelude.RFLAGS.ResumeFlagClear (f.store r) :=
  ⟨(StatusFlags.extractLsb'_store f r 16 (by decide)).trans h.rf⟩

/-- After a form that ends in `writeOutputs … nextIP`, RIP is `nextIP`. -/
theorem afterStep_writeOutputs_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    {n : Nat} (dst : Operand n) (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => writeOutputs t dst (out t) oracleUsed nextIP).RIP = nextIP := by
  cases dst <;>
  simp [afterStep, finishStep, writeOutputs, Operand.write, setFlags, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After a form that ends in `writeFlagsOutputs … nextIP`, RIP is `nextIP`. -/
theorem afterStep_writeFlagsOutputs_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (f : RamState → StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeFlagsOutputs t (f t) oracleUsed nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeFlagsOutputs, setFlags, afterFetches, beforeFetch, resetStepFields,
    h.ready.repeatClear, h.ready.msr]

/--
Preservation. If `s` is ready to step and the instruction's form ends in `writeOutputs` to a
register, the state after the step is ready to step again. Only general-purpose registers, the status
flags, the oracle, `Next_IP`, RIP and per-step bookkeeping change, and none of `ReadyToStep`'s
facts depend on them; TF and RF are not status flags, so they stay clear.
-/
theorem ReadyToStep.afterStep_writeOutputs [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r : BitVec 5) (out : RamState → BitVec n × StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeOutputs t (.reg r) (out t) oracleUsed nextIP) := by
  have hst : SameControls s
      (afterStep s length fun t => writeOutputs t (.reg r) (out t) oracleUsed nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf, StatusFlags.resumeFlagClear_store _ hr.rf,
      hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- Preservation for a form that ends in `writeOutputs` to a no-REX byte register (AL–BL,
AH–BH): it writes register `byteRegGpr r` (`writeOutputs_byteReg`). -/
theorem ReadyToStep.afterStep_writeOutputs_byteReg [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 3) (out : RamState → BitVec 8 × StatusFlags) (oracleUsed : Nat)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeOutputs t (Operand.byteReg r) (out t) oracleUsed nextIP) := by
  simp only [writeOutputs_byteReg]
  exact ReadyToStep.afterStep_writeOutputs h length _ _ oracleUsed nextIP

/--
Preservation for flags-only forms. If `s` is ready to step and the instruction's form ends in
`writeFlagsOutputs`, the state after the step is ready to step again: as for `afterStep_writeOutputs`, with
no register written.
-/
theorem ReadyToStep.afterStep_writeFlagsOutputs [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (f : RamState → StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeFlagsOutputs t (f t) oracleUsed nextIP) := by
  have hst : SameControls s (afterStep s length fun t => writeFlagsOutputs t (f t) oracleUsed nextIP) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    ⟨h.memory.cr3, h.memory.tables⟩,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, StatusFlags.trapFlagClear_store _ hr.tf, StatusFlags.resumeFlagClear_store _ hr.rf,
      hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

end X86Proofs
