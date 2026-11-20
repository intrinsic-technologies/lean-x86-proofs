import X86Proofs.Instructions.Movs.Operation
import X86Proofs.Program.ReadWrite.RepString

/-!
# Layer 2: `REP_MOVSQ_0`

lean-x86's `REP_MOVSQ_0` (`F3 REX.W A5`, `rep movsq`) does one *chunk* per `step`: it sets
`Next_IP`, and if RCX ≠ 0 runs `stride` iterations of `MOV_STRING` (64 bits) and `RCX -= 1`, where
`stride` comes from the `Get_Repeat_String_Stride` binding; finally it sets
`Repeat_String_Operation := (RCX ≠ 0)`. The step wrapper only copies `Next_IP` into RIP when that
flag is false, so RIP stays on the instruction until RCX reaches 0.

With the binding returning stride 1 for positive counts (`Prelude.UnitStringStride`), one step is
one `movsSpec 64` followed by `repCount` (`rep_movsq_form`). With RCX = 0 nothing is copied and the
flag is cleared (`rep_movsq_form_zero`). Behind an FS or GS prefix the source is at
`segBase + RSI` (`rep_movsq_seg_form`, used by the `rep_string` family's `_seg` chain). This is
the one file that unfolds `REP_MOVSQ_0` (architecture rule 5); `rep_movsq_a32_form` and
`rep_movsq_a32_form_zero` are its forms at address size 32 (`67`), and `rep_movsq_down_form`
its form with DF = 1, used by the generated `_a32` and DF = 1 chains.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `REP_MOVSQ_0` with RCX ≠ 0 and 64-bit addresses, in 64-bit mode with no REX2, LOCK or
segment prefix, REX.W set, DF clear and flat DS and ES, with the stride binding answering 1: if the
8 source bytes (at RSI) and the 8 destination bytes (at RDI) lie below 4 GiB and are
present in RAM, the form copies one quadword (`movsSpec 64` from the state with `Next_IP := ip`),
decrements RCX and sets the repeat flag to RCX ≠ 0 (`repCount`).
-/
theorem rep_movsq_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : ctx.rex_w = 1)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : (rsi.read t).toNat + 8 ≤ 2^32)
    (hdst : (rdi.read t).toNat + 8 ≤ 2^32)
    (hsrcMem : ∀ i, i < 8 → (t.external[rsi.read t + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.REP_MOVSQ_0 ip ctx).run t =
      (.ok (), repCount (movsSpec 64 { t with Next_IP := ip })) := by
  have hop := mov_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (.inr (.inr (.inr rfl))) ctx hseg hm64 hds hes hdf hsrc hdst
    hsrcMem hdstMem
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSQ_0
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  have hslice (a : RamState) (v : BitVec 64) : (X86.Runtime.CheckedSlice.read v 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok v, a) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (hslice _ _)).trans ?_
  simp only [hlock, hrex2, hw] at hop
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 64 _ (by
    simp only [X86.Runtime.Unsigned]; have := BitVec.toNat_ne_iff_ne.mpr hcount; simp at this ⊢; omega))]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

/-- Layer 2 for `REP_MOVSQ_0` with RCX = 0: nothing is copied; `Next_IP` is set and the repeat
flag cleared. -/
theorem rep_movsq_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : ctx.rex_w = 1) (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_MOVSQ_0 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_MOVSQ_0
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  have hslice (a : RamState) (v : BitVec 64) : (X86.Runtime.CheckedSlice.read v 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok v, a) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (hslice _ _)).trans ?_
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

/-- Layer 2 for `REP_MOVSQ_0` with RCX ≠ 0 behind an FS or GS prefix: as `rep_movsq_form`, the
source at `segBase ctx.segment + RSI` (`movsSegSpec`). -/
theorem rep_movsq_seg_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 8)
    (hwr : MemWritable t (rdi.read t) 8) :
    (X86.Instructions.REP_MOVSQ_0 ip ctx).run t =
      (.ok (), repCount (movsSegSpec (segBase ctx.segment) 64 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
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
  unfold X86.Instructions.REP_MOVSQ_0
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead64_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 64 _ hpos)]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (checkedSliceRead64_run _ _)]
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

/-- Layer 2 for `REP_MOVSQ_0` with RCX ≠ 0 at address size 32 (a `67` prefix: ESI, EDI, ECX): as
`rep_movsq_form`, with RCX below 4 GiB and the 8 source and destination bytes strictly below
4 GiB, so ESI, EDI and ECX advance as RSI, RDI and RCX do (`mov_string_operation_a32`). -/
theorem rep_movsq_a32_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : ctx.rex_w = 1)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 8) (hwr : MemWritable t (rdi.read t) 8)
    (hsl : (rsi.read t).toNat + 8 < 2^32) (hdl : (rdi.read t).toNat + 8 < 2^32)
    (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REP_MOVSQ_0 ip ctx).run t =
      (.ok (), repCount (movsSpec 64 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hseg hm64 hds hes hdf hsl hdl
    hrd.mem hwr.mem
  have hkeep : rcx.read (movsSpec 64 { t with Next_IP := ip }) = rcx.read t := by
    simp only [movsSpec]
    rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
      Operand.read_reg_write_mem, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]
    rfl
  have h0 : (rcx.read t).toNat ≠ 0 := fun e => hcount (BitVec.eq_of_toNat_eq (by simpa using e))
  have hnz : (X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) ==
      (0 : Int)) = false := by
    rw [beq_eq_false_iff_ne, unsigned_eq]
    show (((rcx.read t).setWidth 32).toNat : Int) ≠ 0
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hcl]
    omega
  have hpos :
      (0 : Int) < X86.Runtime.Unsigned ((rcx.read { t with Next_IP := ip }).setWidth 32) := by
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
  unfold X86.Instructions.REP_MOVSQ_0
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((32 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 32) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (checkedSliceRead32_run _ _)).trans ?_
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 64 _ hpos)]
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

/-- Layer 2 for `REP_MOVSQ_0` with RCX = 0 at address size 32: nothing is copied; `Next_IP` is
set and the repeat flag cleared. -/
theorem rep_movsq_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false) (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1) (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_MOVSQ_0 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_MOVSQ_0
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
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

/-- Layer 2 for `REP_MOVSQ_0` with RCX ≠ 0 and the direction flag set: as `rep_movsq_form`, one
quadword moved with RSI and RDI stepping down (`movsDownSpec 64`), for the `rep_string` family's
DF = 1 chain. -/
theorem rep_movsq_down_form [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hw : ctx.rex_w = 1)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hrd : MemReadable t (rsi.read t) 8) (hwr : MemWritable t (rdi.read t) 8) :
    (X86.Instructions.REP_MOVSQ_0 ip ctx).run t =
      (.ok (), repCount (movsDownSpec 64 { t with Next_IP := ip })) := by
  have hop := mov_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc] at hop ⊢
  unfold X86.Instructions.REP_MOVSQ_0
  simp only [hrex2, hlock, hw, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show ((1 : BitVec 1) == 0) = false from rfl]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  have hslice (a : RamState) (v : BitVec 64) : (X86.Runtime.CheckedSlice.read v 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok v, a) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (hslice _ _)).trans ?_
  simp only [hlock, hrex2, hw] at hop
  have hnz : (X86.Runtime.Unsigned (rcx.read { t with Next_IP := ip }) == (0 : Int)) = false := by
    simp only [x86_runtime, beq_eq_false_iff_ne]
    intro he
    exact hcount (BitVec.eq_of_toNat_eq (by simpa using he))
  rw [hnz]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run _ _ (getRepeatStringStride_run hstride _ 64 _ (by
    simp only [X86.Runtime.Unsigned]; have := BitVec.toNat_ne_iff_ne.mpr hcount
    simp at this ⊢; omega))]
  simp only [show X86.Runtime.intRange 0 ((1 : Int) - 1) = [0] from rfl, List.forIn_cons,
    List.forIn_nil, bind_assoc]
  refine (specM_bind_run _ _ hop).trans ?_
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hsub (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Subtract_int (n := 64) v 1) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok (v - 1), a) := rfl
  rw [specM_bind_run _ _ (hsub _ _), specM_bind_run _ _ (writeRCX64_run _ _)]
  simp only [pure_bind]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run a = (.ok (v == 0#64), a) := rfl
  rw [specM_bind_run _ _ (hzero _ _), rcx_read_write]
  rfl

end X86Proofs
