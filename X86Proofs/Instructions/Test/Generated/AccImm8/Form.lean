import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Test.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem test_al_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (imm : BitVec 8)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.TEST_AL_IMMb ip ctx).run s =
      let dst : Operand 8 := .reg 0
      (.ok (), writeFlagsOutputs t (testSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend 8)) 1
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false, rex2_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.TEST_AL_IMMb
  simp only [Operand.read, writeFlagsOutputs]
  spec_run [
    AL => al_run _,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide) _ _]

end X86Proofs
