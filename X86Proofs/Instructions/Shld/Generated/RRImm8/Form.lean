
import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Shld.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.SHLD

theorem shld_r_r_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) (htmode : In64BitMode t) :
    (X86.Instructions.SHLD_GPRv_GPRv_IMMb ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let c := shiftCount n imm
      (.ok (), writeOutputs t dst
        (shldSpec (fun i => oracleBit (oracleSkip t.oracle i))
          (t.oracle.take n).1 (StatusFlags.ofRFLAGS t.RFLAGS) c
          (dst.read s) (src.read s))
        (shldOracleBits n c) (BitVec.add ip 1#64)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SHLD_GPRv_GPRv_IMMb
    simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.SHLD => shld_operation _ 64 (by decide) _ _ _,
      Write_GPR => writeGPR64_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SHLD_GPRv_GPRv_IMMb
    simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.SHLD => shld_operation _ 32 (by decide) _ _ _,
      Write_GPR => writeGPR32_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem shld_r16_r16_imm8_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (reg rm : BitVec 3) (imm : BitVec 8) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok imm, t)) (htmode : In64BitMode t) :
    (X86.Instructions.SHLD_GPRv_GPRv_IMMb ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let c := shiftCount 16 imm
      (.ok (), writeOutputs t dst
        (shldSpec (fun i => oracleBit (oracleSkip t.oracle i))
          (t.oracle.take 16).1 (StatusFlags.ofRFLAGS t.RFLAGS) c
          (dst.read s) (src.read s))
        (shldOracleBits 16 c) (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SHLD_GPRv_GPRv_IMMb
  simp only [Operand.read_reg16, writeOutputs, Operand.write_reg16]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.SHLD => shld_operation _ 16 (by decide) _ _ _,
    Write_GPR => writeGPR16_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
