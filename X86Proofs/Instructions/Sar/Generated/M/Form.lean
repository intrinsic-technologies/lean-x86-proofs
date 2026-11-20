import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Sar.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

attribute [local irreducible] X86.Instructions.Operations.SAR

theorem sar_m_imm8_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (hu : DataReady u)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (u.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.SAR_MEMv_IMMb ip ctx mod rm).run s =
      let c := shiftCount n imm
      (.ok (), writeRmwOutputs u lin (sarSpec (StatusFlags.ofRFLAGS u.RFLAGS)
          (oracleBit (dataAccess u "load").oracle) (sarOracleAF (dataAccess u "load").oracle c) c
          ((Operand.mem lin : Operand n).read u))
        (sarOracleBits c)
        (BitVec.add next 1#64)) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg u hu seg addr lin hseg 64 (by decide)
      .Memory_Read_Modify_Write (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (k : Nat) (v : BitVec 64) := logicalMemWrite_run_seg
      (writeFlagsOutputs (dataAccess u "load") f k (BitVec.add next 1#64))
      ((hu.dataAccess "load").of_sameControls
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl hu.tables)
      seg addr lin hseg 64 (by decide) v hlow hmem
    unfold X86.Instructions.SAR_MEMv_IMMb
    simp only [writeRmwOutputs, writeFlagsOutputs]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_with hfetch
    spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by
      show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64)) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
      rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.SAR => sar_operation _ 64 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _ _]
  · have hcontext :
        {ctx with operand_size := 32, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg u hu seg addr lin hseg 32 (by decide)
      .Memory_Read_Modify_Write (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (k : Nat) (v : BitVec 32) := logicalMemWrite_run_seg
      (writeFlagsOutputs (dataAccess u "load") f k (BitVec.add next 1#64))
      ((hu.dataAccess "load").of_sameControls
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl hu.tables)
      seg addr lin hseg 32 (by decide) v hlow hmem
    unfold X86.Instructions.SAR_MEMv_IMMb
    simp only [writeRmwOutputs, writeFlagsOutputs]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_with hfetch
    spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by
      show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64)) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
      rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.SAR => sar_operation _ 32 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _ _]

theorem sar_m16_imm8_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (hsize : ctx.operand_size = 16) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (hu : DataReady u)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (u.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.SAR_MEMv_IMMb ip ctx mod rm).run s =
      let c := shiftCount 16 imm
      (.ok (), writeRmwOutputs u lin (sarSpec (StatusFlags.ofRFLAGS u.RFLAGS)
          (oracleBit (dataAccess u "load").oracle) (sarOracleAF (dataAccess u "load").oracle c) c
          ((Operand.mem lin : Operand 16).read u))
        (sarOracleBits c)
        (BitVec.add next 1#64)) := by
  have hcontext :
      {ctx with operand_size := 16, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg u hu seg addr lin hseg 16 (by decide)
    .Memory_Read_Modify_Write (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (k : Nat) (v : BitVec 16) := logicalMemWrite_run_seg
    (writeFlagsOutputs (dataAccess u "load") f k (BitVec.add next 1#64))
    ((hu.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl hu.tables)
    seg addr lin hseg 16 (by decide) v hlow hmem
  unfold X86.Instructions.SAR_MEMv_IMMb
  simp only [writeRmwOutputs, writeFlagsOutputs]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.SAR => sar_operation _ 16 (by decide) _ _,
    Logical_Mem_Write => hwrite _ _ _]

theorem sar_m_one_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (ht : DataReady t)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.SAR_MEMv_ONE ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs t lin (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) (sarOracleAF (dataAccess t "load").oracle 1) 1
          ((Operand.mem lin : Operand n).read t))
        (sarOracleBits 1)
        next) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg t ht seg addr lin hseg 64 (by decide)
      .Memory_Read_Modify_Write (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (k : Nat) (v : BitVec 64) := logicalMemWrite_run_seg
      (writeFlagsOutputs (dataAccess t "load") f k next)
      ((ht.dataAccess "load").of_sameControls
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
      seg addr lin hseg 64 (by decide) v hlow hmem
    unfold X86.Instructions.SAR_MEMv_ONE
    simp only [writeRmwOutputs, writeFlagsOutputs]
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.SAR => sar_operation _ 64 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _ _]
  · have hcontext :
        {ctx with operand_size := 32, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg t ht seg addr lin hseg 32 (by decide)
      .Memory_Read_Modify_Write (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (k : Nat) (v : BitVec 32) := logicalMemWrite_run_seg
      (writeFlagsOutputs (dataAccess t "load") f k next)
      ((ht.dataAccess "load").of_sameControls
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
      seg addr lin hseg 32 (by decide) v hlow hmem
    unfold X86.Instructions.SAR_MEMv_ONE
    simp only [writeRmwOutputs, writeFlagsOutputs]
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.SAR => sar_operation _ 32 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _ _]

theorem sar_m16_one_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (hsize : ctx.operand_size = 16) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (ht : DataReady t)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.SAR_MEMv_ONE ip ctx mod rm).run s =
      (.ok (), writeRmwOutputs t lin (sarSpec (StatusFlags.ofRFLAGS t.RFLAGS)
          (oracleBit (dataAccess t "load").oracle) (sarOracleAF (dataAccess t "load").oracle 1) 1
          ((Operand.mem lin : Operand 16).read t))
        (sarOracleBits 1)
        next) := by
  have hcontext :
      {ctx with operand_size := 16, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 16 (by decide)
    .Memory_Read_Modify_Write (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (k : Nat) (v : BitVec 16) := logicalMemWrite_run_seg
    (writeFlagsOutputs (dataAccess t "load") f k next)
    ((ht.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
    seg addr lin hseg 16 (by decide) v hlow hmem
  unfold X86.Instructions.SAR_MEMv_ONE
  simp only [writeRmwOutputs, writeFlagsOutputs]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.SAR => sar_operation _ 16 (by decide) _ _,
    Logical_Mem_Write => hwrite _ _ _]

end X86Proofs
