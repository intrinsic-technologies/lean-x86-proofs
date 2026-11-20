import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Test.Generated.R8Imm8R1.Decode
import X86Proofs.Instructions.Test.Generated.R8Imm8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem test_r1_r8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex modrm : UInt8) (imm : BitVec 8) (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP (rex :: 0xF6 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_F6_r1 s h rex modrm imm hmod hreg
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0xF6 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0xF6 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 4 h.fetchReady hc hlow' 8 (by decide) imm 3
    (immBytes_getElem?_append [rex, 0xF6, modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [test_r8_imm8_form _ _ (BitVec.add s.RIP 3#64) _ _ imm (hmode 4) rfl rfl himm,
    show BitVec.add (BitVec.add s.RIP 3#64) 1#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0xF6 (modrm :: immBytes 8 imm) hrex
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

theorem test_r1_r8_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) (imm : BitVec 8) :
    let dst : Operand 8 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 4 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 4 _ 1 _

theorem test_r1_r8_imm8_low_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 1) (hrm8 : (modrmRm modrm).toNat < 4)
    (hcode : BytesAt s s.RIP (0xF6 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_F6_r1 s h modrm imm hmod hreg
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0xF6 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (0xF6 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hlow' 8 (by decide) imm 2
    (immBytes_getElem?_append [0xF6, modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [test_r8_imm8_low_form _ _ (BitVec.add s.RIP 2#64) (legacyContext s.DS) (modrmRm modrm) imm (hmode 3)
    (gprNumber_zero_lt_four hrm8) rfl himm,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xF6 (modrm :: immBytes 8 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 4).of_cs_lma_eq rfl rfl)

theorem test_r1_r8_imm8_low_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) (imm : BitVec 8) :
    let dst : Operand 8 := .reg (gprNumber 0 0 (modrmRm modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 3 _ 1 _

theorem test_r1_r8_imm8_norex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (modrm : UInt8) (imm : BitVec 8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 1)
    (hcode : BytesAt s s.RIP (0xF6 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 8 := Operand.byteReg (modrmRm modrm)
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_F6_r1 s h modrm imm hmod hreg
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0xF6 :: modrm :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (0xF6 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hlow' 8
    (by decide) imm 2 (immBytes_getElem?_append [0xF6, modrm] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [test_r8_imm8_gpr8_form _ _ (BitVec.add s.RIP 2#64) (legacyContext s.DS) (modrmRm modrm) imm
      (hmode 3) rfl himm,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xF6 (modrm :: immBytes 8 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode
    ((hmode 4).of_cs_lma_eq rfl rfl)

theorem test_r1_r8_imm8_norex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8)
    (imm : BitVec 8) :
    let dst : Operand 8 := Operand.byteReg (modrmRm modrm)
    ReadyToStep (afterStep s 3 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 3 _ 1 _

end X86Proofs
