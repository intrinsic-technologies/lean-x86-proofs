import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Cmpxchg.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmpxchg_lock_m8_r8_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
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
    (X86.Instructions.CMPXCHG_LOCK_MEMb_GPR8 ip ctx mod reg rm).run s =
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let acc : Operand 8 := .reg 0
      (.ok (), if acc.read t = (Operand.mem lin : Operand 8).read t then
        writeRmwOutputs t lin
          (src.read t, cmpSpec (acc.read t) ((Operand.mem lin : Operand 8).read t)) 0 next
      else
        writeRmwRegOutputs t lin
          ((Operand.mem lin : Operand 8).read t,
            cmpSpec (acc.read t) ((Operand.mem lin : Operand 8).read t)) 0 next 0
          ((Operand.mem lin : Operand 8).read t)) := by
  have hcontext : {ctx with address_size := asz} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg_lock t ht seg addr lin hseg 8 (by decide) hlow
    hmem hlk
  have hwrite (f : StatusFlags) (v : BitVec 8) := logicalMemWrite_run_seg_lock
    (writeFlagsOutputs (dataAccess t "load") f 0 next)
    ((ht.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
    seg addr lin hseg 8 (by decide) v hlow hmem
  have hwrite' (g : Vector (BitVec 64) 32) (f : StatusFlags) (v : BitVec 8) :=
    logicalMemWrite_run_seg_lock (setFlags { dataAccess t "load" with Next_IP := next, GPR := g } f)
    ((ht.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
    seg addr lin hseg 8 (by decide) v hlow hmem
  unfold X86.Instructions.CMPXCHG_LOCK_MEMb_GPR8
  by_cases hc : (Operand.reg 0 : Operand 8).read t = (Operand.mem lin : Operand 8).read t
  · simp only [eq_true hc, ↓reduceIte]
    simp only [Operand.read_reg8] at hc
    simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg8, oracleSkip_zero]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hreg) hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_eq _ 8 (by decide) (t.GPR[gprIndex 0].setWidth 8) _ _ _
          (by rfl) (by exact hc),
      Logical_Mem_Write => hwrite _ _]
  · simp only [eq_false hc, ↓reduceIte]
    simp only [Operand.read_reg8] at hc
    simp only [writeRmwRegOutputs, writeRmwOutputs, writeFlagsOutputs, Operand.read_reg8,
      Operand.write_reg8, oracleSkip_zero]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hreg) hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_ne _ 8 (by decide) (t.GPR[gprIndex 0].setWidth 8) _ _ _
          (by rfl) (by exact hc),
      Logical_Mem_Write => hwrite' _ _ _]

theorem cmpxchg_lock_m8_r8_gpr8_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
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
    (X86.Instructions.CMPXCHG_LOCK_MEMb_GPR8 ip ctx mod reg rm).run s =
      let src : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)
      let acc : Operand 8 := .reg 0
      (.ok (), if acc.read t = (Operand.mem lin : Operand 8).read t then
        writeRmwOutputs t lin
          (src.read t, cmpSpec (acc.read t) ((Operand.mem lin : Operand 8).read t)) 0 next
      else
        writeRmwRegOutputs t lin
          ((Operand.mem lin : Operand 8).read t,
            cmpSpec (acc.read t) ((Operand.mem lin : Operand 8).read t)) 0 next 0
          ((Operand.mem lin : Operand 8).read t)) := by
  have hcontext : {ctx with address_size := asz} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg_lock t ht seg addr lin hseg 8 (by decide) hlow
    hmem hlk
  have hwrite (f : StatusFlags) (v : BitVec 8) := logicalMemWrite_run_seg_lock
    (writeFlagsOutputs (dataAccess t "load") f 0 next)
    ((ht.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
    seg addr lin hseg 8 (by decide) v hlow hmem
  have hwrite' (g : Vector (BitVec 64) 32) (f : StatusFlags) (v : BitVec 8) :=
    logicalMemWrite_run_seg_lock (setFlags { dataAccess t "load" with Next_IP := next, GPR := g } f)
    ((ht.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
    seg addr lin hseg 8 (by decide) v hlow hmem
  unfold X86.Instructions.CMPXCHG_LOCK_MEMb_GPR8
  by_cases hc : (Operand.reg 0 : Operand 8).read t = (Operand.mem lin : Operand 8).read t
  · simp only [eq_true hc, ↓reduceIte]
    simp only [Operand.read_reg8] at hc
    simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg8, oracleSkip_zero]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR8_run_gpr8 _ _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_eq _ 8 (by decide) (t.GPR[gprIndex 0].setWidth 8) _ _ _
          (by rfl) (by exact hc),
      Logical_Mem_Write => hwrite _ _]
  · simp only [eq_false hc, ↓reduceIte]
    simp only [Operand.read_reg8] at hc
    simp only [writeRmwRegOutputs, writeRmwOutputs, writeFlagsOutputs, Operand.read_reg8,
      Operand.write_reg8, oracleSkip_zero]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR8_run_gpr8 _ _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_ne _ 8 (by decide) (t.GPR[gprIndex 0].setWidth 8) _ _ _
          (by rfl) (by exact hc),
      Logical_Mem_Write => hwrite' _ _ _]

end X86Proofs
