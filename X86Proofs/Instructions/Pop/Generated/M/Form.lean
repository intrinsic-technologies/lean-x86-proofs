
import X86Proofs.Program.ReadWrite.PopMem

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pop_m_form [Bindings] {asz : Int} (hasz : asz = 64 ∨ asz = 32) (s t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true)
    (hosz : ctx.osz_prefix_present = false)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip baseUsesRsp : Bool)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64)
    (hseg : SegAccess seg (popMemAdjustedAddr asz.toNat baseUsesRsp addr 64) lin)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 8)
    (hw : MemWritable t lin 8) :
    (X86.Instructions.POP_MEMv ip ctx mod rm).run s =
      (.ok (), (Operand.reg 4 : Operand 64).write
        ((Operand.mem lin : Operand 64).write
          (dataAccess (dataAccess (withNextIP t next) "load") "store")
          ((Operand.mem (stackPtr t) : Operand 64).read t))
        (stackPtr t + BitVec.ofNat 64 (64 / 8))) := by
  have hpop := pop_operation (withNextIP t next)
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) hss (hr.of_external_eq rfl)
  have hwrite (a : BitVec 64) (ha : a = popMemAdjustedAddr asz.toNat baseUsesRsp addr 64) :=
    logicalMemWrite_run_seg (dataAccess (withNextIP t next) "load")
      (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
        rfl h.tables) seg a lin (ha ▸ hseg) 64 (by decide)
      ((Operand.mem (stackPtr t) : Operand 64).read t) hw.low hw.mem
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false,
      address_size := asz, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hea ⊢
  generalize ctx.rex_w = w at hea ⊢
  rcases hasz with rfl | rfl <;> rcases hw1 w with rfl | rfl
  · unfold X86.Instructions.POP_MEMv
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (s := t) (t := withNextIP t next) (value := ()) rfl).trans ?_
    refine (specM_bind_run _ _ hpop).trans ?_
    refine (specM_bind_run _ _ (rsp_run _)).trans ?_
    cases baseUsesRsp
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine (specM_bind_run _ _ (hwrite _ rfl)).trans ?_
      exact writeRSP64_run _ _
    · simp only [↓reduceIte, assert_of_true (show decide ((64 : Int) ≤ 64) = true from rfl),
        assert_of_true (show decide ((0 : Int) ≤ 64) = true from rfl), pure_bind]
      refine (specM_bind_run _ _
        (checkedSliceRead_zero_run _ _ 64 (by decide) (by decide))).trans ?_
      simp only [stdZeroExtend_eq_pure (n := 64) (target := 64) _ (by decide), pure_bind]
      refine (specM_bind_run _ _ (hwrite _ ?_)).trans ?_
      · show ((addr + (stackPtr t + 8 - stackPtr t)).setWidth 64).setWidth 64 = _
        rw [BitVec.add_comm (stackPtr t), BitVec.add_sub_cancel]
        rfl
      exact writeRSP64_run _ _
  · unfold X86.Instructions.POP_MEMv
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (s := t) (t := withNextIP t next) (value := ()) rfl).trans ?_
    refine (specM_bind_run _ _ hpop).trans ?_
    refine (specM_bind_run _ _ (rsp_run _)).trans ?_
    cases baseUsesRsp
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine (specM_bind_run _ _ (hwrite _ rfl)).trans ?_
      exact writeRSP64_run _ _
    · simp only [↓reduceIte, assert_of_true (show decide ((64 : Int) ≤ 64) = true from rfl),
        assert_of_true (show decide ((0 : Int) ≤ 64) = true from rfl), pure_bind]
      refine (specM_bind_run _ _
        (checkedSliceRead_zero_run _ _ 64 (by decide) (by decide))).trans ?_
      simp only [stdZeroExtend_eq_pure (n := 64) (target := 64) _ (by decide), pure_bind]
      refine (specM_bind_run _ _ (hwrite _ ?_)).trans ?_
      · show ((addr + (stackPtr t + 8 - stackPtr t)).setWidth 64).setWidth 64 = _
        rw [BitVec.add_comm (stackPtr t), BitVec.add_sub_cancel]
        rfl
      exact writeRSP64_run _ _
  · unfold X86.Instructions.POP_MEMv
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (s := t) (t := withNextIP t next) (value := ()) rfl).trans ?_
    refine (specM_bind_run _ _ hpop).trans ?_
    refine (specM_bind_run _ _ (rsp_run _)).trans ?_
    cases baseUsesRsp
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine (specM_bind_run _ _ (hwrite _ rfl)).trans ?_
      exact writeRSP64_run _ _
    · simp only [↓reduceIte, assert_of_true (show decide ((32 : Int) ≤ 64) = true from rfl),
        assert_of_true (show decide ((0 : Int) ≤ 32) = true from rfl), pure_bind]
      refine (specM_bind_run _ _
        (checkedSliceRead_zero_run _ _ 32 (by decide) (by decide))).trans ?_
      simp only [stdZeroExtend_eq_pure (n := 32) (target := 64) _ (by decide), pure_bind]
      refine (specM_bind_run _ _ (hwrite _ ?_)).trans ?_
      · show ((addr + (stackPtr t + 8 - stackPtr t)).setWidth 32).setWidth 64 = _
        rw [BitVec.add_comm (stackPtr t), BitVec.add_sub_cancel]
        rfl
      exact writeRSP64_run _ _
  · unfold X86.Instructions.POP_MEMv
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (s := t) (t := withNextIP t next) (value := ()) rfl).trans ?_
    refine (specM_bind_run _ _ hpop).trans ?_
    refine (specM_bind_run _ _ (rsp_run _)).trans ?_
    cases baseUsesRsp
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine (specM_bind_run _ _ (hwrite _ rfl)).trans ?_
      exact writeRSP64_run _ _
    · simp only [↓reduceIte, assert_of_true (show decide ((32 : Int) ≤ 64) = true from rfl),
        assert_of_true (show decide ((0 : Int) ≤ 32) = true from rfl), pure_bind]
      refine (specM_bind_run _ _
        (checkedSliceRead_zero_run _ _ 32 (by decide) (by decide))).trans ?_
      simp only [stdZeroExtend_eq_pure (n := 32) (target := 64) _ (by decide), pure_bind]
      refine (specM_bind_run _ _ (hwrite _ ?_)).trans ?_
      · show ((addr + (stackPtr t + 8 - stackPtr t)).setWidth 32).setWidth 64 = _
        rw [BitVec.add_comm (stackPtr t), BitVec.add_sub_cancel]
        rfl
      exact writeRSP64_run _ _

theorem pop_m16_form [Bindings] {asz : Int} (hasz : asz = 64 ∨ asz = 32) (s t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true)
    (hosz : ctx.osz_prefix_present = true) (hw0 : ctx.rex_w = 0)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip baseUsesRsp : Bool)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64)
    (hseg : SegAccess seg (popMemAdjustedAddr asz.toNat baseUsesRsp addr 16) lin)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 2)
    (hw : MemWritable t lin 2) :
    (X86.Instructions.POP_MEMv ip ctx mod rm).run s =
      (.ok (), (Operand.reg 4 : Operand 64).write
        ((Operand.mem lin : Operand 16).write
          (dataAccess (dataAccess (withNextIP t next) "load") "store")
          ((Operand.mem (stackPtr t) : Operand 16).read t))
        (stackPtr t + BitVec.ofNat 64 (16 / 8))) := by
  have hpop := pop16_operation (withNextIP t next)
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) hss (hr.of_external_eq rfl)
  have hwrite (a : BitVec 64) (ha : a = popMemAdjustedAddr asz.toNat baseUsesRsp addr 16) :=
    logicalMemWrite_run_seg (dataAccess (withNextIP t next) "load")
      (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
        rfl h.tables) seg a lin (ha ▸ hseg) 16 (by decide)
      ((Operand.mem (stackPtr t) : Operand 16).read t) hw.low hw.mem
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := true,
      address_size := asz, lock_prefix_present := false,
      rex_w := 0 } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hea ⊢
  rcases hasz with rfl | rfl
  · unfold X86.Instructions.POP_MEMv
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (s := t) (t := withNextIP t next) (value := ()) rfl).trans ?_
    refine (specM_bind_run _ _ hpop).trans ?_
    refine (specM_bind_run _ _ (rsp_run _)).trans ?_
    cases baseUsesRsp
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine (specM_bind_run _ _ (hwrite _ rfl)).trans ?_
      exact writeRSP64_run _ _
    · simp only [↓reduceIte, assert_of_true (show decide ((64 : Int) ≤ 64) = true from rfl),
        assert_of_true (show decide ((0 : Int) ≤ 64) = true from rfl), pure_bind]
      refine (specM_bind_run _ _
        (checkedSliceRead_zero_run _ _ 64 (by decide) (by decide))).trans ?_
      simp only [stdZeroExtend_eq_pure (n := 64) (target := 64) _ (by decide), pure_bind]
      refine (specM_bind_run _ _ (hwrite _ ?_)).trans ?_
      · show ((addr + (stackPtr t + 2 - stackPtr t)).setWidth 64).setWidth 64 = _
        rw [BitVec.add_comm (stackPtr t), BitVec.add_sub_cancel]
        rfl
      exact writeRSP64_run _ _
  · unfold X86.Instructions.POP_MEMv
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (s := t) (t := withNextIP t next) (value := ()) rfl).trans ?_
    refine (specM_bind_run _ _ hpop).trans ?_
    refine (specM_bind_run _ _ (rsp_run _)).trans ?_
    cases baseUsesRsp
    · simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      refine (specM_bind_run _ _ (hwrite _ rfl)).trans ?_
      exact writeRSP64_run _ _
    · simp only [↓reduceIte, assert_of_true (show decide ((32 : Int) ≤ 64) = true from rfl),
        assert_of_true (show decide ((0 : Int) ≤ 32) = true from rfl), pure_bind]
      refine (specM_bind_run _ _
        (checkedSliceRead_zero_run _ _ 32 (by decide) (by decide))).trans ?_
      simp only [stdZeroExtend_eq_pure (n := 32) (target := 64) _ (by decide), pure_bind]
      refine (specM_bind_run _ _ (hwrite _ ?_)).trans ?_
      · show ((addr + (stackPtr t + 2 - stackPtr t)).setWidth 32).setWidth 64 = _
        rw [BitVec.add_comm (stackPtr t), BitVec.add_sub_cancel]
        rfl
      exact writeRSP64_run _ _

end X86Proofs
