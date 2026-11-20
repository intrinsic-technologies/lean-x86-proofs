import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Mov.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_r8_imm8_c6_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3)
    (hrm : ctx.rex_prefix_present = true ∨
      (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) (imm : BitVec 8)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) (hmode : In64BitMode t) :
    (X86.Instructions.MOV_GPR8_IMMb_C6r0 ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult t dst (movSpec imm) (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOV_GPR8_IMMb_C6r0
  simp only [writeResult, Operand.write_reg8]
  spec_run [
    Mem_Fetch => hfetch]
  dsimp only
  have hv : BitVec.ofInt (Int.toNat 8) imm.toInt = imm := BitVec.ofInt_toInt
  rw [hv]
  exact writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hrm) _ (hmode.of_cs_lma_eq rfl rfl)

theorem mov_r8_imm8_c6_gpr8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3)
    (hlock : ctx.lock_prefix_present = false) (imm : BitVec 8)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) (hmode : In64BitMode t) :
    (X86.Instructions.MOV_GPR8_IMMb_C6r0 ip ctx rm).run s =
      let dst : Operand 8 :=
        .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      (.ok (), writeResult t dst (movSpec imm) (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOV_GPR8_IMMb_C6r0
  simp only [writeResult]
  spec_run [
    Mem_Fetch => hfetch]
  dsimp only
  have hv : BitVec.ofInt (Int.toNat 8) imm.toInt = imm := BitVec.ofInt_toInt
  rw [hv]
  exact writeGPR8_run_gpr8 _ _ _ _ (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
