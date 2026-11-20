import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.Not.Generated.R8.Decode
import X86Proofs.Instructions.Not.Generated.R8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem not_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hrm8 : (modrmRm modrm).toNat < 4)
    (hcode : BytesAt s s.RIP [0xF6, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeResult t dst (notSpec (dst.read t)) (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_F6_not s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [not_r8_form _ _ (legacyContext s.DS) (modrmRm modrm) hmode
    (.inr (gprNumber_zero_lt_four hrm8)) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xF6 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem not_r8_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 2 fun t =>
      writeResult t dst (notSpec (dst.read t)) (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeResult h 2 _ _ _

theorem not_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hcode : BytesAt s s.RIP [rex, 0xF6, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t dst (notSpec (dst.read t)) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_F6_not s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [not_r8_form _ _ (rexContext s.DS rex.toBitVec) (modrmRm modrm) hmode
    (.inl rfl) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0xF6 [modrm] hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem not_r8_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeResult t dst (notSpec (dst.read t)) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeResult h 3 _ _ _

theorem not_r8_norex_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 2)
    (hcode : BytesAt s s.RIP [0xF6, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 8 := Operand.byteReg (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeResult t dst (notSpec (dst.read t)) (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_F6_not s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [not_r8_gpr8_form _ _ (legacyContext s.DS) (modrmRm modrm) hmode rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xF6 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (by simp only [writeResult_byteReg]; exact hmode.of_cs_lma_eq rfl rfl)

theorem not_r8_norex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let dst : Operand 8 := Operand.byteReg (modrmRm modrm)
    ReadyToStep (afterStep s 2 fun t =>
      writeResult t dst (notSpec (dst.read t)) (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeResult_byteReg h 2 _ _ _

end X86Proofs
