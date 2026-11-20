import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xchg.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xchg_lock_m8_r8_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hreg : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (t.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hlk : LockReady t lin (1)) :
    (X86.Instructions.XCHG_MEMb_GPR8_0 ip ctx mod reg rm).run s =
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeRmwRegResult t lin (src.read t) next (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
        ((Operand.mem lin : Operand 8).read t)) := by
  have hcontext : {ctx with address_size := asz} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg_lock t ht seg addr lin hseg 8 (by decide) hlow
    hmem hlk
  have hwrite (v : BitVec 8) := logicalMemWrite_run_seg_lock
    { dataAccess t "load" with Next_IP := next }
    ((ht.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
    seg addr lin hseg 8 (by decide) v hlow hmem
  unfold X86.Instructions.XCHG_MEMb_GPR8_0
  simp only [writeRmwRegResult, writeRmwResult, Operand.read_reg8,
    Operand.write_reg8]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hreg) hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    liftM => xchg_operation _ 8 (by decide) _ _,
    Logical_Mem_Write => hwrite _,
    Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hreg) _
      (by exact hmode.afterRmwResult lin next _)]

theorem xchg_lock_m8_r8_gpr8_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (t.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hlk : LockReady t lin 1) :
    (X86.Instructions.XCHG_MEMb_GPR8_0 ip ctx mod reg rm).run s =
      let src : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)
      (.ok (), writeRmwOpResult t lin (src.read t) next src
        ((Operand.mem lin : Operand 8).read t)) := by
  have hcontext : {ctx with address_size := asz} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg_lock t ht seg addr lin hseg 8 (by decide) hlow
    hmem hlk
  have hwrite (v : BitVec 8) := logicalMemWrite_run_seg_lock
    { dataAccess t "load" with Next_IP := next }
    ((ht.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
    seg addr lin hseg 8 (by decide) v hlow hmem
  unfold X86.Instructions.XCHG_MEMb_GPR8_0
  simp only [writeRmwOpResult, writeRmwResult]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (readGPR8_run_gpr8 _ _ _ hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    liftM => xchg_operation _ 8 (by decide) _ _,
    Logical_Mem_Write => hwrite _,
    Write_GPR8 => writeGPR8_run_gpr8 _ _ _ _
      (by exact hmode.afterRmwResult lin next _)]

end X86Proofs
