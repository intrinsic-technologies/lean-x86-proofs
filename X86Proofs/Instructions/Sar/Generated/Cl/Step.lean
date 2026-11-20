import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.PrefixScan
import X86Proofs.Instructions.Sar.Generated.Cl.Decode
import X86Proofs.Instructions.Sar.Generated.Cl.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem sar_r64_cl_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [rex, 0xD3, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 ((Operand.reg 1 : Operand 8).read s)
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_D3_sar s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [sar_r_cl_form _ _ _ _ hmode 64 (by decide)
    (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0xD3 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem sar_r64_cl_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 64 ((Operand.reg 1 : Operand 8).read s)
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _

theorem sar_r32_cl_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [0xD3, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    let c := shiftCount 32 ((Operand.reg 1 : Operand 8).read s)
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_D3_sar s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [sar_r_cl_form _ _ _ _ hmode 32 (by decide)
    (legacyContext_operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xD3 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem sar_r32_cl_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    let c := shiftCount 32 ((Operand.reg 1 : Operand 8).read s)
    ReadyToStep (afterStep s 2 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeOutputs h 2 _ _ _ _

theorem sar_r32_cl_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [rex, 0xD3, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 ((Operand.reg 1 : Operand 8).read s)
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_D3_sar s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [sar_r_cl_form _ _ _ _ hmode 32 (by decide)
    (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0xD3 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem sar_r32_cl_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 32 ((Operand.reg 1 : Operand 8).read s)
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _

theorem sar_r16_cl_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [0x66, 0xD3, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 16 := .reg (gprNumber 0 0 (modrmRm modrm))
    let c := shiftCount 16 ((Operand.reg 1 : Operand 8).read s)
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_66_D3_sar s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [sar_r16_cl_form _ _ _ _ hmode
    (oszContext_operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_66_legacy0 s _ h 0xD3 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem sar_r16_cl_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (modrm : UInt8) :
    let dst : Operand 16 := .reg (gprNumber 0 0 (modrmRm modrm))
    let c := shiftCount 16 ((Operand.reg 1 : Operand 8).read s)
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _

theorem sar_r16_cl_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7)
    (hcode : BytesAt s s.RIP [0x66, rex, 0xD3, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 16 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 16 ((Operand.reg 1 : Operand 8).read s)
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_66_rex_D3_sar s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [sar_r16_cl_form _ _ _ _ hmode
    (hrex.operand_size_osz s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_66_rex_legacy0 s _ h rex 0xD3 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem sar_r16_cl_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm : UInt8) :
    let dst : Operand 16 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 16 ((Operand.reg 1 : Operand 8).read s)
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (sarOracleAF t.oracle c) c (dst.read t))
        (sarOracleBits c) (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _

end X86Proofs
