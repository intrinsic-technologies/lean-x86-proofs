import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Sub.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem sub_lock_m_imm32_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = asz)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 32)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 32).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 4#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (hu : DataReady u)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (u.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hlk : LockReady u lin (n / 8)) :
    (X86.Instructions.SUB_LOCK_MEMv_IMMz ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs u lin (subSpec
          ((Operand.mem lin : Operand n).read u) (imm.signExtend n)) 0
        (BitVec.add next 4#64)) := by
  rcases hn with rfl | rfl
  · have hread := logicalMemRead_run_seg_lock u hu seg addr lin hseg 64 (by decide) hlow
      hmem hlk
    have hwrite (f : StatusFlags) (v : BitVec 64) := logicalMemWrite_run_seg_lock
      (writeFlagsOutputs (dataAccess u "load") f 0 (BitVec.add next 4#64))
      ((hu.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl rfl rfl rfl rfl hu.tables) seg addr lin hseg 64 (by decide) v hlow hmem
    have hcontext : {ctx with operand_size := 64, address_size := asz} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SUB_LOCK_MEMv_IMMz
    simp only [writeRmwOutputs, writeFlagsOutputs, oracleSkip_zero]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_with hfetch
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by
      show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 4#64)) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
      rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.SUB => sub_operation _ 64 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _]
  · have hread := logicalMemRead_run_seg_lock u hu seg addr lin hseg 32 (by decide) hlow
      hmem hlk
    have hwrite (f : StatusFlags) (v : BitVec 32) := logicalMemWrite_run_seg_lock
      (writeFlagsOutputs (dataAccess u "load") f 0 (BitVec.add next 4#64))
      ((hu.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl rfl rfl rfl rfl hu.tables) seg addr lin hseg 32 (by decide) v hlow hmem
    have hcontext : {ctx with operand_size := 32, address_size := asz} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.SUB_LOCK_MEMv_IMMz
    simp only [writeRmwOutputs, writeFlagsOutputs, oracleSkip_zero]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_with hfetch
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by
      show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 4#64)) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
      rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.SUB => sub_operation _ 32 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _]

theorem sub_lock_m16_imm16_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hsize : ctx.operand_size = 16) (haddr : ctx.address_size = asz)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 16)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 16).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 2#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (hu : DataReady u)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (u.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hlk : LockReady u lin (2)) :
    (X86.Instructions.SUB_LOCK_MEMv_IMMz ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs u lin (subSpec
          ((Operand.mem lin : Operand 16).read u) (imm.signExtend 16)) 0
        (BitVec.add next 2#64)) := by
  have hread := logicalMemRead_run_seg_lock u hu seg addr lin hseg 16 (by decide) hlow
    hmem hlk
  have hwrite (f : StatusFlags) (v : BitVec 16) := logicalMemWrite_run_seg_lock
    (writeFlagsOutputs (dataAccess u "load") f 0 (BitVec.add next 2#64))
    ((hu.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hu.tables) seg addr lin hseg 16 (by decide) v hlow hmem
  have hcontext : {ctx with operand_size := 16, address_size := asz} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.SUB_LOCK_MEMv_IMMz
  simp only [writeRmwOutputs, writeFlagsOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 2#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.SUB => sub_operation _ 16 (by decide) _ _,
    Logical_Mem_Write => hwrite _ _]

end X86Proofs
