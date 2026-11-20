import X86Proofs.Program.ReadWrite.String

/-!
# One string load

`lodsSpec n t`: what one `LODS` of `n` bits does with the direction flag clear: load the `n`-bit
memory operand at RSI into RAX (at 32 bits zero-extended, at 16 and 8 bits merged into the old
value, as any `n`-bit register write) and advance RSI by `n / 8`. The bookkeeping of the data read
(oracle bits and the `load` trace event) is `dataAccess`. `lodsSegSpec base n t`: the same with
an FS/GS segment override, the source read at `base + RSI`.
`lodsDownSpec n t`, `lodsDownSegSpec base n t`: the same with the direction flag set (DF = 1), the
addresses stepping down by `n / 8` (`load_string_operation_down`, `_down_seg`).
-/

namespace X86Proofs

open X86 X86.Machine

/--
One string load of `n` bits with DF = 0, from state `t`: the `n`-bit value at RSI is written to
RAX, then RSI advances by `n / 8`.
-/
def lodsSpec (n : Nat) (t : RamState) : RamState :=
  let u := (Operand.reg 0 : Operand n).write (dataAccess t "load")
    ((Operand.mem (rsi.read t) : Operand n).read t)
  rsi.write u (rsi.read t + BitVec.ofNat 64 (n / 8))

/--
`lodsSpec` with an FS/GS segment override whose base is `base`: the `n`-bit value at `base + RSI`
is written to RAX, then RSI advances by `n / 8`.
-/
def lodsSegSpec (base : BitVec 64) (n : Nat) (t : RamState) : RamState :=
  let u := (Operand.reg 0 : Operand n).write (dataAccess t "load")
    ((Operand.mem (base + rsi.read t) : Operand n).read t)
  rsi.write u (rsi.read t + BitVec.ofNat 64 (n / 8))

/--
One string load of `n` bits with DF = 1, from state `t`: the `n`-bit value at RSI is written to
RAX, then RSI goes back by `n / 8`.
-/
def lodsDownSpec (n : Nat) (t : RamState) : RamState :=
  let u := (Operand.reg 0 : Operand n).write (dataAccess t "load")
    ((Operand.mem (rsi.read t) : Operand n).read t)
  rsi.write u (rsi.read t - BitVec.ofNat 64 (n / 8))

/--
`lodsDownSpec` with an FS/GS segment override whose base is `base`: the `n`-bit value at
`base + RSI`
is written to RAX, then RSI goes back by `n / 8`.
-/
def lodsDownSegSpec (base : BitVec 64) (n : Nat) (t : RamState) : RamState :=
  let u := (Operand.reg 0 : Operand n).write (dataAccess t "load")
    ((Operand.mem (base + rsi.read t) : Operand n).read t)
  rsi.write u (rsi.read t - BitVec.ofNat 64 (n / 8))

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem load_string_operation [Bindings] (t : RamState) (h : DataReady t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hr : MemReadable t (rsi.read t) (n / 8)) :
    (X86.Instructions.Operations.LOAD_STRING 64 n ctx).run t = (.ok (), lodsSpec n t) := by
  have hread : (Logical_Mem_Read (nullDataSegment t.DS) (rsi.read t) n .Memory_Read
      .Normal_Alignment false).run t =
      (.ok ((Operand.mem (rsi.read t) : Operand n).read t), dataAccess t "load") := by
    rw [hds]
    exact logicalMemRead_run t h false (rsi.read t) n hn .Memory_Read (.inl rfl) hr.low hr.mem
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  have hrax (u : RamState) (v : BitVec n) :
      (Write_RAX (size := (n : Int)) v).run u = (.ok (), (Operand.reg 0 : Operand n).write u v) :=
    writeRAX_run_of_nat u n hn v
  unfold X86.Instructions.Operations.LOAD_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ (hrax _ _)).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact hdf
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (rsiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRSI64_run _ _).trans ?_
    simp only [lodsSpec, Operand.read_reg_dataAccess, ofInt_div8,
      Operand.read_write_reg_of_ne _ (show (0 : BitVec 5) ≠ 6 by decide)]

theorem load_string_operation_seg [Bindings] (t : RamState) (h : DataReady t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = true) (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hr : MemReadable t (segBase ctx.segment + rsi.read t) (n / 8)) :
    (X86.Instructions.Operations.LOAD_STRING 64 n ctx).run t =
      (.ok (), lodsSegSpec (segBase ctx.segment) n t) := by
  have hread := logicalMemRead_run_seg t h ctx.segment (rsi.read t) _ (hsr.access _) n hn
    .Memory_Read (.inl rfl) hr.low hr.mem
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok ctx.segment :=
    fun seg => getEffectiveSegment_run_of_seg ctx seg hseg
  have hrax (u : RamState) (v : BitVec n) :
      (Write_RAX (size := (n : Int)) v).run u = (.ok (), (Operand.reg 0 : Operand n).write u v) :=
    writeRAX_run_of_nat u n hn v
  unfold X86.Instructions.Operations.LOAD_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ (hrax _ _)).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact hdf
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (rsiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRSI64_run _ _).trans ?_
    simp only [lodsSegSpec, Operand.read_reg_dataAccess, ofInt_div8,
      Operand.read_write_reg_of_ne _ (show (0 : BitVec 5) ≠ 6 by decide)]

theorem load_string_operation_down [Bindings] (t : RamState) (h : DataReady t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hr : MemReadable t (rsi.read t) (n / 8)) :
    (X86.Instructions.Operations.LOAD_STRING 64 n ctx).run t = (.ok (), lodsDownSpec n t) := by
  have hread : (Logical_Mem_Read (nullDataSegment t.DS) (rsi.read t) n .Memory_Read
      .Normal_Alignment false).run t =
      (.ok ((Operand.mem (rsi.read t) : Operand n).read t), dataAccess t "load") := by
    rw [hds]
    exact logicalMemRead_run t h false (rsi.read t) n hn .Memory_Read (.inl rfl) hr.low hr.mem
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  have hrax (u : RamState) (v : BitVec n) :
      (Write_RAX (size := (n : Int)) v).run u = (.ok (), (Operand.reg 0 : Operand n).write u v) :=
    writeRAX_run_of_nat u n hn v
  unfold X86.Instructions.Operations.LOAD_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ (hrax _ _)).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlagSet_run _ ?_)).trans ?_
    · exact hdf
    simp (config := { decide := true }) only [↓reduceIte]
    refine (specM_bind_run _ _ (rsiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRSI64_run _ _).trans ?_
    simp only [lodsDownSpec, Operand.read_reg_dataAccess, ofInt_neg_div8, ← BitVec.sub_eq_add_neg,
      Operand.read_write_reg_of_ne _ (show (0 : BitVec 5) ≠ 6 by decide)]

theorem load_string_operation_down_seg [Bindings] (t : RamState) (h : DataReady t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = true) (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hr : MemReadable t (segBase ctx.segment + rsi.read t) (n / 8)) :
    (X86.Instructions.Operations.LOAD_STRING 64 n ctx).run t =
      (.ok (), lodsDownSegSpec (segBase ctx.segment) n t) := by
  have hread := logicalMemRead_run_seg t h ctx.segment (rsi.read t) _ (hsr.access _) n hn
    .Memory_Read (.inl rfl) hr.low hr.mem
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok ctx.segment :=
    fun seg => getEffectiveSegment_run_of_seg ctx seg hseg
  have hrax (u : RamState) (v : BitVec n) :
      (Write_RAX (size := (n : Int)) v).run u = (.ok (), (Operand.reg 0 : Operand n).write u v) :=
    writeRAX_run_of_nat u n hn v
  unfold X86.Instructions.Operations.LOAD_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ (hrax _ _)).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlagSet_run _ ?_)).trans ?_
    · exact hdf
    simp (config := { decide := true }) only [↓reduceIte]
    refine (specM_bind_run _ _ (rsiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRSI64_run _ _).trans ?_
    simp only [lodsDownSegSpec, Operand.read_reg_dataAccess, ofInt_neg_div8,
      ← BitVec.sub_eq_add_neg,
      Operand.read_write_reg_of_ne _ (show (0 : BitVec 5) ≠ 6 by decide)]

theorem load_string_operation_a32 [Bindings] (t : RamState) (h : DataReady t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hr : MemReadable t (rsi.read t) (n / 8))
    (hlt : (rsi.read t).toNat + n / 8 < 2^32) :
    (X86.Instructions.Operations.LOAD_STRING 32 n ctx).run t = (.ok (), lodsSpec n t) := by
  have hread : (Logical_Mem_Read (nullDataSegment t.DS) (rsi.read t) n .Memory_Read
      .Normal_Alignment false).run t =
      (.ok ((Operand.mem (rsi.read t) : Operand n).read t), dataAccess t "load") := by
    rw [hds]
    exact logicalMemRead_run t h false (rsi.read t) n hn .Memory_Read (.inl rfl) hr.low hr.mem
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  have hrax (u : RamState) (v : BitVec n) :
      (Write_RAX (size := (n : Int)) v).run u = (.ok (), (Operand.reg 0 : Operand n).write u v) :=
    writeRAX_run_of_nat u n hn v
  have ha : ((rsi.read t).setWidth 32).setWidth 64 = rsi.read t :=
    setWidth32_setWidth64_of_lt (by omega)
  unfold X86.Instructions.Operations.LOAD_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice32_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend32_run _ _)).trans ?_
    rw [ha]
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ (hrax _ _)).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact hdf
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (rsiSlice32_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt32_run _ _ _)).trans ?_
    refine (writeRSI32_run _ _).trans ?_
    simp only [lodsSpec, Operand.read_reg_dataAccess, ofInt32_div8,
      Operand.read_write_reg_of_ne _ (show (0 : BitVec 5) ≠ 6 by decide)]
    rw [setWidth64_add_of_lt (by omega)]

end X86Proofs
