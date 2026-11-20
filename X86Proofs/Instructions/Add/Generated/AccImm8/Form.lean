import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Add.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem add_al_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (imm : BitVec 8)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) :
    (X86.Instructions.ADD_AL_IMMb ip ctx).run s =
      let dst : Operand 8 := .reg 0
      (.ok (), writeOutputs t dst (addSpec (dst.read s) (imm.signExtend 8)) 0
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ADD_AL_IMMb
  simp only [Operand.read, writeOutputs, Operand.write, oracleSkip_zero]
  spec_run [
    AL => al_run _,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.ADD => add_operation _ 8 (by decide) _ _,
    AL_write => alWrite_run _ _]

end X86Proofs
