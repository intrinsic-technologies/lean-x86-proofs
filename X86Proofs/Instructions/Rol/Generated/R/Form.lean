import X86Proofs.Core.Operand
import X86Proofs.Instructions.Rol.Operation

namespace X86Proofs

open X86 X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.ROL

theorem rol_r_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ROL_GPRv_IMMb ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount n count
      (.ok (), writeOutputs t dst (rolSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read s)) (rolOracleBits c)
        (BitVec.add ip 1#64)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.ROL_GPRv_IMMb
    simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.ROL => rol_operation _ 64 (by decide) _ _,
      Write_GPR => writeGPR64_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.ROL_GPRv_IMMb
    simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.ROL => rol_operation _ 32 (by decide) _ _,
      Write_GPR => writeGPR32_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem rol_r16_imm8_form [X86.Machine.Bindings] (s t : X86.Machine.RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (rm : BitVec 3) (count : BitVec 8)
    (hmode : In64BitMode s) (hfetch : (Mem_Fetch ip 8).run s = (.ok count, t))
    (htmode : In64BitMode t)
    (hsize : ctx.operand_size = 16) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ROL_GPRv_IMMb ip ctx rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 16 count
      (.ok (), writeOutputs t dst (rolSpec (StatusFlags.ofRFLAGS t.RFLAGS)
        (oracleBit t.oracle) c (dst.read s)) (rolOracleBits c)
        (BitVec.add ip 1#64)) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ROL_GPRv_IMMb
  simp only [Operand.read_reg16, writeOutputs, Operand.write_reg16]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.ROL => rol_operation _ 16 (by decide) _ _,
    Write_GPR => writeGPR16_run _ _ _ (htmode.of_cs_lma_eq rfl rfl)]

theorem rol_r_one_form [X86.Machine.Bindings] (s : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s) (n : Nat)
    (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ROL_GPRv_ONE ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (rolSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) 1 (dst.read s)) (rolOracleBits 1) ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.ROL_GPRv_ONE
    simp only [Operand.read_reg64, writeOutputs, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      X86.Instructions.Operations.ROL => rol_operation _ 64 (by decide) _ _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.ROL_GPRv_ONE
    simp only [Operand.read_reg32, writeOutputs, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      X86.Instructions.Operations.ROL => rol_operation _ 32 (by decide) _ _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem rol_r16_one_form [X86.Machine.Bindings] (s : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ROL_GPRv_ONE ip ctx rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeOutputs s dst (rolSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) 1 (dst.read s)) (rolOracleBits 1) ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ROL_GPRv_ONE
  simp only [Operand.read_reg16, writeOutputs, Operand.write_reg16]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.ROL => rol_operation _ 16 (by decide) _ _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
