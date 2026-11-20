import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.PrefixScan
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Test.Generated.AccImm32.Decode
import X86Proofs.Instructions.Test.Generated.AccImm32.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem test_rax_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex : UInt8) (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec)
    (hcode : BytesAt s s.RIP (rex :: 0xA9 :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 6 ≤ 2^32) :
    let dst : Operand 64 := .reg 0
    X86.Machine.step s = some (.next (afterStep s 6 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 64)) 1
        (BitVec.add s.RIP 6#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_A9_acc s h rex imm
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0xA9 :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (rex :: 0xA9 :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hlow' 32 (by decide) imm 2
    (immBytes_getElem?_append [rex, 0xA9] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [test_rax_imm32_form _ _ (BitVec.add s.RIP 2#64) _ imm 64 (by decide) (hrex.operand_size s.DS) rfl rfl himm,
    show BitVec.add (BitVec.add s.RIP 2#64) 4#64 = BitVec.add s.RIP 6#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_rex_legacy0 s _ h rex 0xA9 (immBytes 32 imm) hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 7).of_cs_lma_eq rfl rfl)

theorem test_rax_imm32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 32) :
    let dst : Operand 64 := .reg 0
    ReadyToStep (afterStep s 6 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 64)) 1
        (BitVec.add s.RIP 6#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 6 _ 1 _

theorem test_eax_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (0xA9 :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 5 ≤ 2^32) :
    let dst : Operand 32 := .reg 0
    X86.Machine.step s = some (.next (afterStep s 5 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 32)) 1
        (BitVec.add s.RIP 5#64))) := by
  have hdecode := decodeLegacy0_run_of_A9_acc s h imm
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0xA9 :: immBytes 32 imm) := hcode
  have hlow' : s.RIP.toNat + (0xA9 :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 2 h.fetchReady hc hlow' 32 (by decide) imm 1
    (immBytes_getElem?_append [0xA9] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [test_rax_imm32_form _ _ (BitVec.add s.RIP 1#64) _ imm 32 (by decide) (legacyContext_operand_size s.DS) rfl rfl himm,
    show BitVec.add (BitVec.add s.RIP 1#64) 4#64 = BitVec.add s.RIP 5#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0xA9 (immBytes 32 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 6).of_cs_lma_eq rfl rfl)

theorem test_eax_imm32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 32) :
    let dst : Operand 32 := .reg 0
    ReadyToStep (afterStep s 5 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 32)) 1
        (BitVec.add s.RIP 5#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 5 _ 1 _

theorem test_ax_imm16_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : BitVec 16)
    (hcode : BytesAt s s.RIP (0x66 :: 0xA9 :: immBytes 16 imm))
    (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 16 := .reg 0
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 16)) 1
        (BitVec.add s.RIP 4#64))) := by
  have hdecode := decodeLegacy0_run_of_66_A9_acc s h imm
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x66 :: 0xA9 :: immBytes 16 imm) := hcode
  have hlow' : s.RIP.toNat + (0x66 :: 0xA9 :: immBytes 16 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 3 h.fetchReady hc hlow' 16 (by decide) imm 2
    (immBytes_getElem?_append [0x66, 0xA9] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [test_ax_imm16_form _ _ (BitVec.add s.RIP 2#64) _ imm (oszContext_operand_size s.DS) rfl rfl himm,
    show BitVec.add (BitVec.add s.RIP 2#64) 2#64 = BitVec.add s.RIP 4#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_66_legacy0 s _ h 0xA9 (immBytes 16 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 5).of_cs_lma_eq rfl rfl)

theorem test_ax_imm16_ready [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 16) :
    let dst : Operand 16 := .reg 0
    ReadyToStep (afterStep s 4 fun t =>
      writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 16)) 1
        (BitVec.add s.RIP 4#64)) :=
  ReadyToStep.afterStep_writeFlagsOutputs h 4 _ 1 _

end X86Proofs
