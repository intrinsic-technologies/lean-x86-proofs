import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.Imul.Generated.R8.Decode
import X86Proofs.Instructions.Imul.Generated.R8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem imul_r8_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hrm8 : (modrmRm modrm).toNat < 4)
    (hcode : BytesAt s s.RIP [0xF6, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let src : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      let r := imulWideSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 0 : Operand 8).read t) (src.read t)
      writeOutputs t (.reg 0 : Operand 16) (r.2.1 ++ r.1, r.2.2) 4 (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_F6_imul s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [imul_r8_form _ _ (legacyContext s.DS) (modrmRm modrm) hmode
    (.inr (gprNumber_zero_lt_four hrm8)) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xF6 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem imul_r8_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let src : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 2 fun t =>
      let r := imulWideSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 0 : Operand 8).read t) (src.read t)
      writeOutputs t (.reg 0 : Operand 16) (r.2.1 ++ r.1, r.2.2) 4 (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeOutputs h 2 _ _ 4 _

theorem imul_r8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hcode : BytesAt s s.RIP [rex, 0xF6, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let src : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      let r := imulWideSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 0 : Operand 8).read t) (src.read t)
      writeOutputs t (.reg 0 : Operand 16) (r.2.1 ++ r.1, r.2.2) 4 (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_F6_imul s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [imul_r8_form _ _ (rexContext s.DS rex.toBitVec) (modrmRm modrm) hmode
    (.inl rfl) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xF6 [modrm] hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem imul_r8_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let src : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t =>
      let r := imulWideSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 0 : Operand 8).read t) (src.read t)
      writeOutputs t (.reg 0 : Operand 16) (r.2.1 ++ r.1, r.2.2) 4 (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ 4 _

theorem imul_r8_norex_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hcode : BytesAt s s.RIP [0xF6, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let src : Operand 8 := Operand.byteReg (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      let r := imulWideSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 0 : Operand 8).read t) (src.read t)
      writeOutputs t (.reg 0 : Operand 16) (r.2.1 ++ r.1, r.2.2) 4 (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_F6_imul s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [imul_r8_gpr8_form _ _ (legacyContext s.DS) (modrmRm modrm) hmode rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xF6 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem imul_r8_norex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let src : Operand 8 := Operand.byteReg (modrmRm modrm)
    ReadyToStep (afterStep s 2 fun t =>
      let r := imulWideSpec (fun i => oracleBit (oracleSkip t.oracle i))
            ((Operand.reg 0 : Operand 8).read t) (src.read t)
      writeOutputs t (.reg 0 : Operand 16) (r.2.1 ++ r.1, r.2.2) 4 (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeOutputs h 2 _ _ 4 _

end X86Proofs
