import X86Proofs.Instructions.Scas.Operation
import X86Proofs.Program.ReadWrite.RepString

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem repne_scasq_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.REPNE_SCASQ ip ctx).run t =
      some (.ok (), repneScasSpec 64 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASQ
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  have hpos : (0 : Int) < X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) := by
    rw [unsigned_eq]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp at this ⊢
    omega
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 64 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX64_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after 64 { t with Next_IP := ip } _

theorem repne_scasq_down_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.REPNE_SCASQ ip ctx).run t =
      some (.ok (), repneScasDownSpec 64 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation_down { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASQ
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  have hpos : (0 : Int) < X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) := by
    rw [unsigned_eq]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp at this ⊢
    omega
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 64 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX64_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after_down 64 { t with Next_IP := ip } _

theorem repne_scasq_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_SCASQ ip ctx).run t =
      some (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REPNE_SCASQ
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [partialSpecM_modify_bind_run]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz', partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  rfl

theorem repne_scasd_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.REPNE_SCASD_2 ip ctx).run t =
      some (.ok (), repneScasSpec 32 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  have hpos : (0 : Int) < X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) := by
    rw [unsigned_eq]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp at this ⊢
    omega
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 32 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX64_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after 32 { t with Next_IP := ip } _

theorem repne_scasd_down_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.REPNE_SCASD_2 ip ctx).run t =
      some (.ok (), repneScasDownSpec 32 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation_down { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  have hpos : (0 : Int) < X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) := by
    rw [unsigned_eq]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp at this ⊢
    omega
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 32 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX64_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after_down 32 { t with Next_IP := ip } _

theorem repne_scasd_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_SCASD_2 ip ctx).run t =
      some (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REPNE_SCASD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [partialSpecM_modify_bind_run]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz', partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  rfl

theorem repne_scasw_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.REPNE_SCASW_2 ip ctx).run t =
      some (.ok (), repneScasSpec 16 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  have hpos : (0 : Int) < X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) := by
    rw [unsigned_eq]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp at this ⊢
    omega
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 16 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX64_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after 16 { t with Next_IP := ip } _

theorem repne_scasw_down_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.REPNE_SCASW_2 ip ctx).run t =
      some (.ok (), repneScasDownSpec 16 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation_down { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  have hpos : (0 : Int) < X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) := by
    rw [unsigned_eq]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp at this ⊢
    omega
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 16 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX64_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after_down 16 { t with Next_IP := ip } _

theorem repne_scasw_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_SCASW_2 ip ctx).run t =
      some (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REPNE_SCASW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [partialSpecM_modify_bind_run]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz', partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  rfl

theorem repne_scasb_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.REPNE_SCASB ip ctx).run t =
      some (.ok (), repneScasSpec 8 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASB
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  have hpos : (0 : Int) < X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) := by
    rw [unsigned_eq]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp at this ⊢
    omega
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 8 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX64_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after 8 { t with Next_IP := ip } _

theorem repne_scasb_down_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.REPNE_SCASB ip ctx).run t =
      some (.ok (), repneScasDownSpec 8 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation_down { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASB
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  have hpos : (0 : Int) < X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) := by
    rw [unsigned_eq]
    have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp at this ⊢
    omega
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 8 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX64_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after_down 8 { t with Next_IP := ip } _

theorem repne_scasb_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_SCASB ip ctx).run t =
      some (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REPNE_SCASB
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run u = some (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [partialSpecM_modify_bind_run]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz', partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  rfl

theorem repne_scasq_a32_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 8)
    (hdl : (rdi.read t).toNat + 8 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REPNE_SCASQ ip ctx).run t =
      some (.ok (), repneScasSpec 64 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation_a32 { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hes hdf (hrd.of_external_eq rfl) hdl
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASQ
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run u =
        some (.ok (x.setWidth 32), u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
  have hnz : (X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) ==
      (0 : Int)) = false := by
    rw [beq_eq_false_iff_ne, unsigned_eq]
    show (((rcx.read t).setWidth 32).toNat : Int) ≠ 0
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hpos : (0 : Int) < X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) := by
    rw [unsigned_eq]
    show (0 : Int) < (((rcx.read t).setWidth 32).toNat : Int)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hsub (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Subtract_int (n := 32) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 64 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX32_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after_a32 64 { t with Next_IP := ip } hcl hcount _

theorem repne_scasq_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_SCASQ ip ctx).run t =
      some (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REPNE_SCASQ
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run u =
        some (.ok (x.setWidth 32), u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned ((0 : BitVec 64).setWidth 32) == (0 : Int)) = true from rfl,
    ↓reduceIte]
  rw [partialSpecM_modify_bind_run]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz', partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  rfl

theorem repne_scasd_a32_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 4)
    (hdl : (rdi.read t).toNat + 4 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REPNE_SCASD_2 ip ctx).run t =
      some (.ok (), repneScasSpec 32 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation_a32 { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hes hdf (hrd.of_external_eq rfl) hdl
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run u =
        some (.ok (x.setWidth 32), u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
  have hnz : (X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) ==
      (0 : Int)) = false := by
    rw [beq_eq_false_iff_ne, unsigned_eq]
    show (((rcx.read t).setWidth 32).toNat : Int) ≠ 0
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hpos : (0 : Int) < X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) := by
    rw [unsigned_eq]
    show (0 : Int) < (((rcx.read t).setWidth 32).toNat : Int)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hsub (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Subtract_int (n := 32) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 32 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX32_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after_a32 32 { t with Next_IP := ip } hcl hcount _

theorem repne_scasd_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_SCASD_2 ip ctx).run t =
      some (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REPNE_SCASD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run u =
        some (.ok (x.setWidth 32), u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned ((0 : BitVec 64).setWidth 32) == (0 : Int)) = true from rfl,
    ↓reduceIte]
  rw [partialSpecM_modify_bind_run]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz', partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  rfl

theorem repne_scasw_a32_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 2)
    (hdl : (rdi.read t).toNat + 2 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REPNE_SCASW_2 ip ctx).run t =
      some (.ok (), repneScasSpec 16 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation_a32 { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hes hdf (hrd.of_external_eq rfl) hdl
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run u =
        some (.ok (x.setWidth 32), u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
  have hnz : (X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) ==
      (0 : Int)) = false := by
    rw [beq_eq_false_iff_ne, unsigned_eq]
    show (((rcx.read t).setWidth 32).toNat : Int) ≠ 0
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hpos : (0 : Int) < X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) := by
    rw [unsigned_eq]
    show (0 : Int) < (((rcx.read t).setWidth 32).toNat : Int)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hsub (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Subtract_int (n := 32) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 16 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX32_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after_a32 16 { t with Next_IP := ip } hcl hcount _

theorem repne_scasw_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_SCASW_2 ip ctx).run t =
      some (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REPNE_SCASW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run u =
        some (.ok (x.setWidth 32), u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned ((0 : BitVec 64).setWidth 32) == (0 : Int)) = true from rfl,
    ↓reduceIte]
  rw [partialSpecM_modify_bind_run]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz', partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  rfl

theorem repne_scasb_a32_form [inst : Bindings]
    (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rdi.read t) 1)
    (hdl : (rdi.read t).toNat + 1 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REPNE_SCASB ip ctx).run t =
      some (.ok (), repneScasSpec 8 { t with Next_IP := ip, Repeat_String_Operation := true }) := by
  have hop := scan_string_operation_a32 { t with Next_IP := ip }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hes hdf (hrd.of_external_eq rfl) hdl
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REPNE_SCASB
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run u =
        some (.ok (x.setWidth 32), u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
  have hnz : (X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) ==
      (0 : Int)) = false := by
    rw [beq_eq_false_iff_ne, unsigned_eq]
    show (((rcx.read t).setWidth 32).toNat : Int) ≠ 0
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hpos : (0 : Int) < X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) := by
    rw [unsigned_eq]
    show (0 : Int) < (((rcx.read t).setWidth 32).toNat : Int)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hsub (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Subtract_int (n := 32) v 1) :
        X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run a =
        some (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [partialSpecM_liftTotal_bind_run _ _ (getRepeatStringStride_run hstride _ 8 _ hpos)]
  rw [partialSpecM_forIn_eq]
  refine' (partialSpecM_bind_run _ _ (partialSpecM_loop_yield_run _ 0 _ _ ?b1 ?b2)).trans ?after
  case b1 =>
    simp only [show decide ((1 : Int) > 0) = true from rfl, ↓reduceIte]
    refine (partialSpecM_liftTotal_bind_run _ _ hop).trans ?_
    rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
      partialSpecM_bind_run _ _ (hsub _ _),
      partialSpecM_liftTotal_bind_run _ _ (writeRCX32_run _ _)]
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
    rw [partialSpecM_get_bind_run]
    split <;> rfl
  case b2 =>
    apply partialSpecM_loop_done_run
    simp only [show decide ((0 : Int) > 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  case after => exact repne_scan_after_a32 8 { t with Next_IP := ip } hcl hcount _

theorem repne_scasb_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_SCASB ip ctx).run t =
      some (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REPNE_SCASB
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  have hslice (u : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run u =
        some (.ok (x.setWidth 32), u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_modify_bind_run, partialSpecM_get_bind_run]
  refine partialSpecM_tryCatch_run _ _ ?_
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned ((0 : BitVec 64).setWidth 32) == (0 : Int)) = true from rfl,
    ↓reduceIte]
  rw [partialSpecM_modify_bind_run]
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz', partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  rfl

end X86Proofs
