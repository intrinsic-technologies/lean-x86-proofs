import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Xor.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xor_m_r_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = asz)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.XOR_MEMv_GPRv ip ctx mod reg rm).run s =
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeRmwOutputs t lin (xorSpec (oracleBit (dataAccess t "load").oracle)
          ((Operand.mem lin : Operand n).read t) (src.read t)) 1 next) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, address_size := asz} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg t ht seg addr lin hseg 64 (by decide)
      .Memory_Read_Modify_Write (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (v : BitVec 64) := logicalMemWrite_run_seg
      (writeFlagsOutputs (dataAccess t "load") f 1 next)
      ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl rfl rfl rfl rfl ht.tables) seg addr lin hseg 64 (by decide) v hlow hmem
    unfold X86.Instructions.XOR_MEMv_GPRv
    simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg64]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR64_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.XOR => xor_operation _ 64 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _]
  · have hcontext : {ctx with operand_size := 32, address_size := asz} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg t ht seg addr lin hseg 32 (by decide)
      .Memory_Read_Modify_Write (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (v : BitVec 32) := logicalMemWrite_run_seg
      (writeFlagsOutputs (dataAccess t "load") f 1 next)
      ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl rfl rfl rfl rfl ht.tables) seg addr lin hseg 32 (by decide) v hlow hmem
    unfold X86.Instructions.XOR_MEMv_GPRv
    simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg32]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR32_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.XOR => xor_operation _ 32 (by decide) _ _,
      Logical_Mem_Write => hwrite _ _]

theorem xor_m16_r16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 16) (haddr : ctx.address_size = asz)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.XOR_MEMv_GPRv ip ctx mod reg rm).run s =
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeRmwOutputs t lin (xorSpec (oracleBit (dataAccess t "load").oracle)
          ((Operand.mem lin : Operand 16).read t) (src.read t)) 1 next) := by
  have hcontext : {ctx with operand_size := 16, address_size := asz} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 16 (by decide)
    .Memory_Read_Modify_Write (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (v : BitVec 16) := logicalMemWrite_run_seg
    (writeFlagsOutputs (dataAccess t "load") f 1 next)
    ((ht.dataAccess "load").of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl ht.tables) seg addr lin hseg 16 (by decide) v hlow hmem
  unfold X86.Instructions.XOR_MEMv_GPRv
  simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg16]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (readGPR16_run _ _ hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.XOR => xor_operation _ 16 (by decide) _ _,
    Logical_Mem_Write => hwrite _ _]

end X86Proofs
