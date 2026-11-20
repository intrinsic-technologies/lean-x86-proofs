import X86Proofs.Instructions.Movs.Operation
import X86Proofs.Program.ReadWrite.RepString

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem rep_movsd_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 4) (hwr : MemWritable t (rdi.read t) 4) :
    (X86.Instructions.REP_MOVSD_2 ip ctx).run t =
      (.ok (), repCount (movsSpec 32 { t with Next_IP := ip })) := by
  have hop := mov_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
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
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 32 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsd_down_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 4) (hwr : MemWritable t (rdi.read t) 4) :
    (X86.Instructions.REP_MOVSD_2 ip ctx).run t =
      (.ok (), repCount (movsDownSpec 32 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
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
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 32 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsd_seg_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 4) (hwr : MemWritable t (rdi.read t) 4) :
    (X86.Instructions.REP_MOVSD_2 ip ctx).run t =
      (.ok (), repCount (movsSegSpec (segBase ctx.segment) 32 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
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
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 32 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsd_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_MOVSD_2 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_MOVSD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

theorem rep_movsw_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 2) (hwr : MemWritable t (rdi.read t) 2) :
    (X86.Instructions.REP_MOVSW_2 ip ctx).run t =
      (.ok (), repCount (movsSpec 16 { t with Next_IP := ip })) := by
  have hop := mov_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
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
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 16 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsw_down_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 2) (hwr : MemWritable t (rdi.read t) 2) :
    (X86.Instructions.REP_MOVSW_2 ip ctx).run t =
      (.ok (), repCount (movsDownSpec 16 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
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
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 16 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsw_seg_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 2) (hwr : MemWritable t (rdi.read t) 2) :
    (X86.Instructions.REP_MOVSW_2 ip ctx).run t =
      (.ok (), repCount (movsSegSpec (segBase ctx.segment) 16 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
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
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 16 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsw_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_MOVSW_2 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_MOVSW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

theorem rep_movsb_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 1) (hwr : MemWritable t (rdi.read t) 1) :
    (X86.Instructions.REP_MOVSB_0 ip ctx).run t =
      (.ok (), repCount (movsSpec 8 { t with Next_IP := ip })) := by
  have hop := mov_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
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
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSB_0
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 8 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsb_down_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 1) (hwr : MemWritable t (rdi.read t) 1) :
    (X86.Instructions.REP_MOVSB_0 ip ctx).run t =
      (.ok (), repCount (movsDownSpec 8 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
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
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSB_0
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 8 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsb_seg_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 1) (hwr : MemWritable t (rdi.read t) 1) :
    (X86.Instructions.REP_MOVSB_0 ip ctx).run t =
      (.ok (), repCount (movsSegSpec (segBase ctx.segment) 8 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
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
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSB_0
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 8 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

theorem rep_movsb_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_MOVSB_0 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_MOVSB_0
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

theorem rep_movsd_a32_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 4) (hwr : MemWritable t (rdi.read t) 4)
    (hsl : (rsi.read t).toNat + 4 < 2^32) (hdl : (rdi.read t).toNat + 4 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REP_MOVSD_2 ip ctx).run t =
      (.ok (), repCount (movsSpec 32 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hseg hm64 hds hes hdf hsl hdl
    hrd.mem hwr.mem
  have hkeep : rcx.read (movsSpec 32 { t with Next_IP := ip }) = rcx.read t := by
    simp only [movsSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_reg_write_mem, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
    rfl
  have hnz : (X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) ==
      (0 : Int)) = false := by
    have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [beq_eq_false_iff_ne, unsigned_eq]
    show (((rcx.read t).setWidth 32).toNat : Int) ≠ 0
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hpos : (0 : Int) < X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) := by
    have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [unsigned_eq]
    show (0 : Int) < (((rcx.read t).setWidth 32).toNat : Int)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hsub (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Subtract_int (n := 32) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#32), a) := rfl
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead32_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 32 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead32_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX32_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead32_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  unfold repCount
  rw [hkeep, setWidth64_sub_one_of_lt hcl hcount,
    setWidth32_beq_zero_of_lt (toNat_sub_one_lt_of_lt hcl hcount)]
  rfl

theorem rep_movsd_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_MOVSD_2 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_MOVSD_2
  simp only [hrex2, hlock, hosz, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead32_run _ _)).trans ?_
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned ((0 : BitVec 64).setWidth 32) == (0 : Int)) = true from rfl,
    ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead32_run _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

theorem rep_movsw_a32_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 2) (hwr : MemWritable t (rdi.read t) 2)
    (hsl : (rsi.read t).toNat + 2 < 2^32) (hdl : (rdi.read t).toNat + 2 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REP_MOVSW_2 ip ctx).run t =
      (.ok (), repCount (movsSpec 16 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hseg hm64 hds hes hdf hsl hdl
    hrd.mem hwr.mem
  have hkeep : rcx.read (movsSpec 16 { t with Next_IP := ip }) = rcx.read t := by
    simp only [movsSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_reg_write_mem, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
    rfl
  have hnz : (X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) ==
      (0 : Int)) = false := by
    have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [beq_eq_false_iff_ne, unsigned_eq]
    show (((rcx.read t).setWidth 32).toNat : Int) ≠ 0
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hpos : (0 : Int) < X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) := by
    have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [unsigned_eq]
    show (0 : Int) < (((rcx.read t).setWidth 32).toNat : Int)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hsub (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Subtract_int (n := 32) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#32), a) := rfl
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead32_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 16 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead32_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX32_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead32_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  unfold repCount
  rw [hkeep, setWidth64_sub_one_of_lt hcl hcount,
    setWidth32_beq_zero_of_lt (toNat_sub_one_lt_of_lt hcl hcount)]
  rfl

theorem rep_movsw_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_MOVSW_2 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_MOVSW_2
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((0 : BitVec 1) == 1) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead32_run _ _)).trans ?_
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned ((0 : BitVec 64).setWidth 32) == (0 : Int)) = true from rfl,
    ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead32_run _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

theorem rep_movsb_a32_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 1) (hwr : MemWritable t (rdi.read t) 1)
    (hsl : (rsi.read t).toNat + 1 < 2^32) (hdl : (rdi.read t).toNat + 1 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REP_MOVSB_0 ip ctx).run t =
      (.ok (), repCount (movsSpec 8 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hseg hm64 hds hes hdf hsl hdl
    hrd.mem hwr.mem
  have hkeep : rcx.read (movsSpec 8 { t with Next_IP := ip }) = rcx.read t := by
    simp only [movsSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_reg_write_mem, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
    rfl
  have hnz : (X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) ==
      (0 : Int)) = false := by
    have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [beq_eq_false_iff_ne, unsigned_eq]
    show (((rcx.read t).setWidth 32).toNat : Int) ≠ 0
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hpos : (0 : Int) < X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) := by
    have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
    rw [unsigned_eq]
    show (0 : Int) < (((rcx.read t).setWidth 32).toNat : Int)
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hsub (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Subtract_int (n := 32) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run a = (.ok (v - 1), a) := rfl
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#32), a) := rfl
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSB_0
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead32_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 8 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead32_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX32_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead32_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  unfold repCount
  rw [hkeep, setWidth64_sub_one_of_lt hcl hcount,
    setWidth32_beq_zero_of_lt (toNat_sub_one_lt_of_lt hcl hcount)]
  rfl

theorem rep_movsb_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_MOVSB_0 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_MOVSB_0
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead32_run _ _)).trans ?_
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned ((0 : BitVec 64).setWidth 32) == (0 : Int)) = true from rfl,
    ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead32_run _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

end X86Proofs
