import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.And.Generated.AccImm8.Decode
import X86Proofs.Instructions.And.Generated.AccImm8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem and_al_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (0x24 :: immBytes 8 imm))
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 8 := .reg 0
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_24_acc s h imm
    hcode hlow
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (0x24 :: immBytes 8 imm) := hcode
  have hlow' : s.RIP.toNat + (0x24 :: immBytes 8 imm).length ≤ 2^32 := by
    simpa using hlow
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) 2 h.fetchReady hc hlow' 8 (by decide) imm 1
    (immBytes_getElem?_append [0x24] imm) (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [and_al_imm8_form _ _ (BitVec.add s.RIP 1#64) _ imm rfl himm,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc _ _ _] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeOutputs, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_none_legacy0 s _ h 0x24 (immBytes 8 imm)
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode ((hmode 3).of_cs_lma_eq rfl rfl)

theorem and_al_imm8_ready [Bindings] {s : RamState} (h : ReadyToStep s) (imm : BitVec 8) :
    let dst : Operand 8 := .reg 0
    ReadyToStep (afterStep s 2 fun t =>
      writeOutputs t dst (andSpec (oracleBit t.oracle) (dst.read t) (imm.signExtend 8)) 1
        (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeOutputs h 2 _ _ 1 _

end X86Proofs
