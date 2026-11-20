import X86Proofs.Core.Operand
import X86Proofs.Instructions.Rol.Operation

namespace X86Proofs

open X86 X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.ROL

theorem rol_r8_cl_form [X86.Machine.Bindings] (s : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hrm : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_b4 ctx.rex_b3 rm).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ROL_GPR8_CL ip ctx rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
      (.ok (), writeOutputs s dst (rolSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) c (dst.read s)) (rolOracleBits c) ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ROL_GPR8_CL
  simp only [Operand.read_reg8, writeOutputs, Operand.write_reg8]
  spec_run [
    Read_GPR8 => readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) hmode,
    CL => cl_run _,
    X86.Instructions.Operations.ROL => rol_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex ‹_›) _
      (hmode.of_cs_lma_eq rfl rfl)]

theorem rol_r8_cl_gpr8_form [X86.Machine.Bindings] (s : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode : In64BitMode s)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.ROL_GPR8_CL ip ctx rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 rm) (byteRex ctx)
      let c := shiftCount 8 ((Operand.reg 1 : Operand 8).read s)
      (.ok (), writeOutputs s dst (rolSpec (StatusFlags.ofRFLAGS s.RFLAGS)
        (oracleBit s.oracle) c (dst.read s)) (rolOracleBits c) ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.ROL_GPR8_CL
  simp only [Operand.read_reg8, writeOutputs]
  spec_run [
    Read_GPR8 => readGPR8_run_gpr8 _ _ _ hmode,
    CL => cl_run _,
    X86.Instructions.Operations.ROL => rol_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_gpr8 _ _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
