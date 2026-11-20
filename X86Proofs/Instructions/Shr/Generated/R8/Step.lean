import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Instructions.Shr.Generated.R8.Decode
import X86Proofs.Instructions.Shr.Generated.R8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem shr_r8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm imm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hrm8 : (modrmRm modrm).toNat < 4)
    (hcode : BytesAt s s.RIP [0xC0, modrm, imm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    let c := shiftCount 8 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_C0_shr s h modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  rw [shr_r8_imm8_form _ _ _ (legacyContext s.DS) (modrmRm modrm) _ (hmode 3) himm (hmode 4)
    (.inr (gprNumber_zero_lt_four hrm8)) rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xC0 [modrm, imm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 4).of_cs_lma_eq rfl rfl)

theorem shr_r8_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (modrm imm : UInt8) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    let c := shiftCount 8 imm.toBitVec
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _

theorem shr_r8_imm8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm imm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hcode : BytesAt s s.RIP [rex, 0xC0, modrm, imm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 8 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_C0_shr s h rex modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 3#64) 8).run (afterFetches (beforeFetch s) 4) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 5) :=
    memFetch_run_of_bytesAt (beforeFetch s) 4 h.fetchReady hcode hlow 3 (by simp) (by decide)
  rw [shr_r8_imm8_form _ _ _ (rexContext s.DS rex.toBitVec) (modrmRm modrm) _ (hmode 4) himm (hmode 5)
    (.inl rfl) rfl,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc s.RIP 3#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0xC0 [modrm, imm] hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

theorem shr_r8_imm8_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm imm : UInt8) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let c := shiftCount 8 imm.toBitVec
    ReadyToStep (afterStep s 4 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeOutputs h 4 _ _ _ _

theorem shr_r8_one_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hrm8 : (modrmRm modrm).toNat < 4)
    (hcode : BytesAt s s.RIP [0xD0, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 1) 1 (dst.read t))
        (shrOracleBits 1) (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_D0_shr s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [shr_r8_one_form _ _ (legacyContext s.DS) (modrmRm modrm) hmode
    (.inr (gprNumber_zero_lt_four hrm8)) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xD0 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem shr_r8_one_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (modrm : UInt8) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 2 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 1) 1 (dst.read t))
        (shrOracleBits 1) (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeOutputs h 2 _ _ _ _

theorem shr_r8_one_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hcode : BytesAt s s.RIP [rex, 0xD0, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 1) 1 (dst.read t))
        (shrOracleBits 1) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_D0_shr s h rex modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [shr_r8_one_form _ _ (rexContext s.DS rex.toBitVec) (modrmRm modrm) hmode
    (.inl rfl) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0xD0 [modrm] hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

theorem shr_r8_one_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (rex modrm : UInt8) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 1) 1 (dst.read t))
        (shrOracleBits 1) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs h 3 _ _ _ _

theorem shr_r8_imm8_norex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm imm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hcode : BytesAt s s.RIP [0xC0, modrm, imm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := Operand.byteReg (modrmRm modrm)
    let c := shiftCount 8 imm.toBitVec
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_C0_shr s h modrm imm hmod hreg hcode hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have himm : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok imm.toBitVec, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  rw [shr_r8_imm8_gpr8_form _ _ _ (legacyContext s.DS) (modrmRm modrm) _ (hmode 3) himm (hmode 4)
      rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xC0 [modrm, imm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (by simp only [writeOutputs_byteReg]; exact (hmode 4).of_cs_lma_eq rfl rfl)

theorem shr_r8_imm8_norex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (modrm imm : UInt8) :
    let dst : Operand 8 := Operand.byteReg (modrmRm modrm)
    let c := shiftCount 8 imm.toBitVec
    ReadyToStep (afterStep s 3 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle c) c (dst.read t))
        (shrOracleBits c) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeOutputs_byteReg h 3 _ _ _ _

theorem shr_r8_one_norex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5)
    (hcode : BytesAt s s.RIP [0xD0, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 8 := Operand.byteReg (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 1) 1 (dst.read t))
        (shrOracleBits 1) (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_D0_shr s h modrm hmod hreg hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [shr_r8_one_gpr8_form _ _ (legacyContext s.DS) (modrmRm modrm) hmode rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xD0 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode
    (by simp only [writeOutputs_byteReg]; exact hmode.of_cs_lma_eq rfl rfl)

theorem shr_r8_one_norex_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (modrm : UInt8) :
    let dst : Operand 8 := Operand.byteReg (modrmRm modrm)
    ReadyToStep (afterStep s 2 fun t =>
      writeOutputs t dst (shrSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) (shrOracleAF t.oracle 1) 1 (dst.read t))
        (shrOracleBits 1) (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeOutputs_byteReg h 2 _ _ _ _

end X86Proofs
