import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WritePair
import X86Proofs.Instructions.Div.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem div_r8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false)
    (hdef : DivDefined ((Operand.reg 0 : Operand 16).read s) ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 8).read s)) :
    (X86.Instructions.DIV_GPR8 ip ctx rm).run s =
      let src : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let r := divSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 0 : Operand 16).read s) (src.read s)
      (.ok (), writeOutputs s (.reg 0 : Operand 16) (r.2.1 ++ r.1, r.2.2) 6 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.DIV_GPR8
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
    X86.Instructions.Operations.DIV => div_operation8 _ _ (by exact hdef)]

theorem div_r8_gpr8_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false)
    (hdef : DivDefined ((Operand.reg 0 : Operand 16).read s)
      ((Operand.gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)).read s)) :
    (X86.Instructions.DIV_GPR8 ip ctx rm).run s =
      let src : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      let r := divSpec (fun i => oracleBit (oracleSkip s.oracle i))
        ((Operand.reg 0 : Operand 16).read s) (src.read s)
      (.ok (), writeOutputs s (.reg 0 : Operand 16) (r.2.1 ++ r.1, r.2.2) 6 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.DIV_GPR8
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    X86.Instructions.Operations.DIV => div_operation8 _ _ (by exact hdef)]

end X86Proofs
