import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Cmpxchg.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmpxchg_m_r_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (haddr : ctx.address_size = asz)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.CMPXCHG_MEMv_GPRv ip ctx mod reg rm).run s =
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let acc : Operand n := .reg 0
      (.ok (), if acc.read t = (Operand.mem lin : Operand n).read t then
        writeRmwOutputs t lin
          (src.read t, cmpSpec (acc.read t) ((Operand.mem lin : Operand n).read t)) 0 next
      else
        writeRmwRegOutputs t lin
          ((Operand.mem lin : Operand n).read t,
            cmpSpec (acc.read t) ((Operand.mem lin : Operand n).read t)) 0 next 0
          ((Operand.mem lin : Operand n).read t)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, address_size := asz} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg t ht seg addr lin hseg 64 (by decide)
      .Memory_Read_Modify_Write (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (v : BitVec 64) := logicalMemWrite_run_seg
      (writeFlagsOutputs (dataAccess t "load") f 0 next)
      ((ht.dataAccess "load").of_sameControls
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
      seg addr lin hseg 64 (by decide) v hlow hmem
    have hwrite' (g : Vector (BitVec 64) 32) (f : StatusFlags) (v : BitVec 64) :=
      logicalMemWrite_run_seg (setFlags { dataAccess t "load" with Next_IP := next, GPR := g } f)
      ((ht.dataAccess "load").of_sameControls
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
      seg addr lin hseg 64 (by decide) v hlow hmem
    unfold X86.Instructions.CMPXCHG_MEMv_GPRv
    by_cases hc : (Operand.reg 0 : Operand 64).read t = (Operand.mem lin : Operand 64).read t
    · simp only [eq_true hc, ↓reduceIte]
      simp only [Operand.read_reg64] at hc
      simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg64, oracleSkip_zero]
      refine (specM_bind_run _ _ hea).trans ?_
      spec_bind_rfl
      spec_bind_rfl
      spec_bind_with (readGPR64_run _ _ hmode)
      refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
      spec_run [
        Logical_Mem_Read => hread,
        X86.Instructions.Operations.CMPXCHG =>
          cmpxchg_operation_eq _ 64 (by decide) t.GPR[gprIndex 0] _ _ _
            (by exact BitVec.setWidth_eq _) (by exact hc),
        Logical_Mem_Write => hwrite _ _]
    · simp only [eq_false hc, ↓reduceIte]
      simp only [Operand.read_reg64] at hc
      simp only [writeRmwRegOutputs, writeRmwOutputs, writeFlagsOutputs, Operand.read_reg64,
        oracleSkip_zero]
      refine (specM_bind_run _ _ hea).trans ?_
      spec_bind_rfl
      spec_bind_rfl
      spec_bind_with (readGPR64_run _ _ hmode)
      refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
      spec_run [
        Logical_Mem_Read => hread,
        X86.Instructions.Operations.CMPXCHG =>
          cmpxchg_operation_ne _ 64 (by decide) t.GPR[gprIndex 0] _ _ _
            (by exact BitVec.setWidth_eq _) (by exact hc),
        Logical_Mem_Write => hwrite' _ _ _]
  · have hcontext : {ctx with operand_size := 32, address_size := asz} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg t ht seg addr lin hseg 32 (by decide)
      .Memory_Read_Modify_Write (.inr rfl) hlow hmem
    have hwrite (f : StatusFlags) (v : BitVec 32) := logicalMemWrite_run_seg
      (writeFlagsOutputs (dataAccess t "load") f 0 next)
      ((ht.dataAccess "load").of_sameControls
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
      seg addr lin hseg 32 (by decide) v hlow hmem
    have hwrite' (g : Vector (BitVec 64) 32) (f : StatusFlags) (v : BitVec 32) :=
      logicalMemWrite_run_seg (setFlags { dataAccess t "load" with Next_IP := next, GPR := g } f)
      ((ht.dataAccess "load").of_sameControls
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
      seg addr lin hseg 32 (by decide) v hlow hmem
    unfold X86.Instructions.CMPXCHG_MEMv_GPRv
    by_cases hc : (Operand.reg 0 : Operand 32).read t = (Operand.mem lin : Operand 32).read t
    · simp only [eq_true hc, ↓reduceIte]
      simp only [Operand.read_reg32] at hc
      simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg32, oracleSkip_zero]
      refine (specM_bind_run _ _ hea).trans ?_
      spec_bind_rfl
      spec_bind_rfl
      spec_bind_with (readGPR32_run _ _ hmode)
      refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
      spec_run [
        Logical_Mem_Read => hread,
        X86.Instructions.Operations.CMPXCHG =>
          cmpxchg_operation_eq _ 32 (by decide) (t.GPR[gprIndex 0].setWidth 32) _ _ _
            (by rfl) (by exact hc),
        Logical_Mem_Write => hwrite _ _]
    · simp only [eq_false hc, ↓reduceIte]
      simp only [Operand.read_reg32] at hc
      simp only [writeRmwRegOutputs, writeRmwOutputs, writeFlagsOutputs, Operand.read_reg32,
        Operand.write_reg32, oracleSkip_zero]
      refine (specM_bind_run _ _ hea).trans ?_
      spec_bind_rfl
      spec_bind_rfl
      spec_bind_with (readGPR32_run _ _ hmode)
      refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
      spec_run [
        Logical_Mem_Read => hread,
        X86.Instructions.Operations.CMPXCHG =>
          cmpxchg_operation_ne _ 32 (by decide) (t.GPR[gprIndex 0].setWidth 32) _ _ _
            (by rfl) (by exact hc),
        Logical_Mem_Write => hwrite' _ _ _]

theorem cmpxchg_m16_r16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 16)
    (haddr : ctx.address_size = asz)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.CMPXCHG_MEMv_GPRv ip ctx mod reg rm).run s =
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let acc : Operand 16 := .reg 0
      (.ok (), if acc.read t = (Operand.mem lin : Operand 16).read t then
        writeRmwOutputs t lin
          (src.read t, cmpSpec (acc.read t) ((Operand.mem lin : Operand 16).read t)) 0 next
      else
        writeRmwRegOutputs t lin
          ((Operand.mem lin : Operand 16).read t,
            cmpSpec (acc.read t) ((Operand.mem lin : Operand 16).read t)) 0 next 0
          ((Operand.mem lin : Operand 16).read t)) := by
  have hcontext : {ctx with operand_size := 16, address_size := asz} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 16 (by decide)
    .Memory_Read_Modify_Write (.inr rfl) hlow hmem
  have hwrite (f : StatusFlags) (v : BitVec 16) := logicalMemWrite_run_seg
    (writeFlagsOutputs (dataAccess t "load") f 0 next)
    ((ht.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
    seg addr lin hseg 16 (by decide) v hlow hmem
  have hwrite' (g : Vector (BitVec 64) 32) (f : StatusFlags) (v : BitVec 16) :=
    logicalMemWrite_run_seg (setFlags { dataAccess t "load" with Next_IP := next, GPR := g } f)
    ((ht.dataAccess "load").of_sameControls
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl ht.tables)
    seg addr lin hseg 16 (by decide) v hlow hmem
  unfold X86.Instructions.CMPXCHG_MEMv_GPRv
  by_cases hc : (Operand.reg 0 : Operand 16).read t = (Operand.mem lin : Operand 16).read t
  · simp only [eq_true hc, ↓reduceIte]
    simp only [Operand.read_reg16] at hc
    simp only [writeRmwOutputs, writeFlagsOutputs, Operand.read_reg16, oracleSkip_zero]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR16_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_eq _ 16 (by decide) (t.GPR[gprIndex 0].setWidth 16) _ _ _
          (by rfl) (by exact hc),
      Logical_Mem_Write => hwrite _ _]
  · simp only [eq_false hc, ↓reduceIte]
    simp only [Operand.read_reg16] at hc
    simp only [writeRmwRegOutputs, writeRmwOutputs, writeFlagsOutputs, Operand.read_reg16,
      Operand.write_reg16, oracleSkip_zero]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_with (readGPR16_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.CMPXCHG =>
        cmpxchg_operation_ne _ 16 (by decide) (t.GPR[gprIndex 0].setWidth 16) _ _ _
          (by rfl) (by exact hc),
      Logical_Mem_Write => hwrite' _ _ _]

end X86Proofs
