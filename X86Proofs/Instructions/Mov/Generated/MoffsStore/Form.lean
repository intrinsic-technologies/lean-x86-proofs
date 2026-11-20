import X86Proofs.Step.Address
import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Mov.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_m_rax_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16) (hsize : ctx.operand_size = n)
    (haddr : ctx.address_size = asz) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (seg : Segment) (moffs next : BitVec 64)
    (hoff : (Direct_Memory_Offset asz ctx ip).run s = (.ok (seg, moffs, next), t))
    (hrip : Handle_RIP_Relative_Address asz false moffs next = .ok moffs)
    (lin : BitVec 64) (hseg : SegAccess seg moffs lin)
    (ht : DataReady t) (hw : MemWritable t lin (n / 8)) :
    (X86.Instructions.MOV_MEMv_OrAX ip ctx).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand n)
        (movSpec ((Operand.reg 0 : Operand n).read t)) next) := by
  rcases hn with rfl | rfl | rfl
  · have hcontext :
        {ctx with
          operand_size := 64, address_size := asz, rex2_prefix_present := false,
          lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg moffs lin hseg 64
      (by decide) ((Operand.reg 0 : Operand 64).read t) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_OrAX
    refine (specM_bind_run _ _ hoff).trans ?_
    simp only [hrip]
    spec_run [
      RAX => rax_run _,
      X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ 64 (by decide) (by decide),
      Logical_Mem_Write => hwrite]
  · have hcontext :
        {ctx with
          operand_size := 32, address_size := asz, rex2_prefix_present := false,
          lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg moffs lin hseg 32
      (by decide) ((Operand.reg 0 : Operand 32).read t) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_OrAX
    refine (specM_bind_run _ _ hoff).trans ?_
    simp only [hrip]
    spec_run [
      RAX => rax_run _,
      X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ 32 (by decide) (by decide),
      Logical_Mem_Write => hwrite]
  · have hcontext :
        {ctx with
          operand_size := 16, address_size := asz, rex2_prefix_present := false,
          lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg moffs lin hseg 16
      (by decide) ((Operand.reg 0 : Operand 16).read t) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_OrAX
    refine (specM_bind_run _ _ hoff).trans ?_
    simp only [hrip]
    spec_run [
      RAX => rax_run _,
      X86.Runtime.CheckedSlice.read => checkedSliceRead_zero_run _ _ 16 (by decide) (by decide),
      Logical_Mem_Write => hwrite]

theorem mov_m8_al_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (haddr : ctx.address_size = asz) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (seg : Segment) (moffs next : BitVec 64)
    (hoff : (Direct_Memory_Offset asz ctx ip).run s = (.ok (seg, moffs, next), t))
    (hrip : Handle_RIP_Relative_Address asz false moffs next = .ok moffs)
    (lin : BitVec 64) (hseg : SegAccess seg moffs lin)
    (ht : DataReady t) (hw : MemWritable t lin (1)) :
    (X86.Instructions.MOV_MEMb_AL ip ctx).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 8)
        (movSpec ((Operand.reg 0 : Operand 8).read t)) next) := by
  have hcontext :
      {ctx with
        address_size := asz, rex2_prefix_present := false,
        lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg moffs lin hseg 8
    (by decide) ((Operand.reg 0 : Operand 8).read t) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMb_AL
  refine (specM_bind_run _ _ hoff).trans ?_
  simp only [hrip]
  spec_run [
    AL => al_run _,
    Logical_Mem_Write => hwrite]

end X86Proofs
