import X86Proofs.Step.Fetch
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Xor.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem xor_rax_imm32_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (imm : BitVec 32)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 32).run s = (.ok imm, t)) :
    (X86.Instructions.XOR_OrAX_IMMz ip ctx).run s =
      let dst : Operand n := .reg 0
      (.ok (), writeOutputs t dst (xorSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend n)) 1
        (BitVec.add ip 4#64)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.XOR_OrAX_IMMz
    simp only [Operand.read, writeOutputs, Operand.write]
    spec_run [
      RAX => rax_run _,
      X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ _ (by decide) (by decide),
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.XOR => xor_operation _ 64 (by decide) _ _,
      Write_RAX => writeRAX_run _ 64 (by decide) _]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.XOR_OrAX_IMMz
    simp only [Operand.read, writeOutputs, Operand.write]
    spec_run [
      RAX => rax_run _,
      X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ _ (by decide) (by decide),
      Mem_Fetch => hfetch,
      X86.Instructions.Operations.XOR => xor_operation _ 32 (by decide) _ _,
      Write_RAX => writeRAX_run _ 32 (by decide) _]

theorem xor_ax_imm16_form [X86.Machine.Bindings] (s t : X86.Machine.RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (imm : BitVec 16)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) (hfetch : (Mem_Fetch ip 16).run s = (.ok imm, t)) :
    (X86.Instructions.XOR_OrAX_IMMz ip ctx).run s =
      let dst : Operand 16 := .reg 0
      (.ok (), writeOutputs t dst (xorSpec (oracleBit t.oracle) (dst.read s) (imm.signExtend 16)) 1
        (BitVec.add ip 2#64)) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.XOR_OrAX_IMMz
  simp only [Operand.read, writeOutputs, Operand.write]
  spec_run [
    RAX => rax_run _,
    X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ _ (by decide) (by decide),
    Mem_Fetch => hfetch,
    X86.Instructions.Operations.XOR => xor_operation _ 16 (by decide) _ _,
    Write_RAX => writeRAX_run _ 16 (by decide) _]

end X86Proofs
