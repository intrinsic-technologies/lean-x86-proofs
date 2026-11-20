import X86Proofs.Program.ReadWrite.String

/-!
# One string move

`movsSpec n t`: what one `MOVS` of `n` bits does with the direction flag clear: copy the `n`-bit
memory operand at RSI to the one at RDI and advance RSI and RDI by `n / 8`. Memory is read and
written through `Operand.mem`; the bookkeeping of the two data accesses (oracle bits and the
`load`/`store` trace events) is `dataAccess`. `movsSegSpec base n t`: the same with an FS/GS
segment override, the source read at `base + RSI`.
`movsDownSpec n t`, `movsDownSegSpec base n t`: the same with the direction flag set (DF = 1), the
addresses stepping down by `n / 8` (`mov_string_operation_down`, `_down_seg`).
-/

namespace X86Proofs

open X86 X86.Machine

/--
One string move of `n` bits with DF = 0, from state `t`: the `n`-bit value at RSI is stored at
RDI, then RSI and RDI each advance by `n / 8`.
-/
def movsSpec (n : Nat) (t : RamState) : RamState :=
  let src : Operand n := .mem (rsi.read t)
  let dst : Operand n := .mem (rdi.read t)
  let u := dst.write (dataAccess (dataAccess t "load") "store") (src.read t)
  rdi.write (rsi.write u (rsi.read t + BitVec.ofNat 64 (n / 8))) (rdi.read t + BitVec.ofNat 64 (n / 8))

/--
`movsSpec` with an FS/GS segment override whose base is `base`: the source is read at
`base + RSI` (the destination ES:RDI takes no override), then RSI and RDI each advance by `n / 8`.
-/
def movsSegSpec (base : BitVec 64) (n : Nat) (t : RamState) : RamState :=
  let src : Operand n := .mem (base + rsi.read t)
  let dst : Operand n := .mem (rdi.read t)
  let u := dst.write (dataAccess (dataAccess t "load") "store") (src.read t)
  rdi.write (rsi.write u (rsi.read t + BitVec.ofNat 64 (n / 8))) (rdi.read t + BitVec.ofNat 64 (n / 8))

/--
One string move of `n` bits with DF = 1, from state `t`: the `n`-bit value at RSI is stored at
RDI, then RSI and RDI each go back by `n / 8`.
-/
def movsDownSpec (n : Nat) (t : RamState) : RamState :=
  let src : Operand n := .mem (rsi.read t)
  let dst : Operand n := .mem (rdi.read t)
  let u := dst.write (dataAccess (dataAccess t "load") "store") (src.read t)
  rdi.write (rsi.write u (rsi.read t - BitVec.ofNat 64 (n / 8)))
    (rdi.read t - BitVec.ofNat 64 (n / 8))

/--
`movsDownSpec` with an FS/GS segment override whose base is `base`: the source is read at
`base + RSI` (the destination ES:RDI takes no override), then RSI and RDI each go back by `n / 8`.
-/
def movsDownSegSpec (base : BitVec 64) (n : Nat) (t : RamState) : RamState :=
  let src : Operand n := .mem (base + rsi.read t)
  let dst : Operand n := .mem (rdi.read t)
  let u := dst.write (dataAccess (dataAccess t "load") "store") (src.read t)
  rdi.write (rsi.write u (rsi.read t - BitVec.ofNat 64 (n / 8)))
    (rdi.read t - BitVec.ofNat 64 (n / 8))

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_string_operation [Bindings] (t : RamState) (h : DataReady t) (hmode : In64BitMode t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : (rsi.read t).toNat + n / 8 ≤ 2^32)
    (hdst : (rdi.read t).toNat + n / 8 ≤ 2^32)
    (hsrcMem : ∀ i, i < n / 8 → (t.external[rsi.read t + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < n / 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.Operations.MOV_STRING 64 n ctx).run t = (.ok (), movsSpec n t) := by
  have hread := logicalMemRead_run t h false (rsi.read t) n hn .Memory_Read (.inl rfl)
    hsrc hsrcMem
  have hu : DataReady (dataAccess t "load") := h.dataAccess _
  have hwrite := logicalMemWrite_run (dataAccess t "load") hu false (rdi.read t) n hn
    ((Operand.mem (rsi.read t) : Operand n).read t) hdst hdstMem
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 0, u) := by
    change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
    rw [hu, show BitVec.extractLsb' 10 1 t.RFLAGS = dfBit t.RFLAGS from rfl, hdf]
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  unfold X86.Instructions.Operations.MOV_STRING
  simp only [hges]
  have hg (u : RamState) : (get : X86.Runtime.SpecM X86.Exception RamState RamState).run u =
      (.ok u, u) := rfl
  have hslice (x : BitVec 64) (u : RamState) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hadd (x : BitVec 64) (k : Int) (u : RamState) :
      (liftM (Std.Bits.Add_int (n := 64) x k) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u =
        (.ok (x + BitVec.ofInt 64 k), u) := rfl
  have hrsi (u : RamState) : (do
      let x ← (RSI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rsi.read u), u) :=
    (specM_bind_run _ _ (rsi_run u)).trans (hslice _ u)
  have hrdi (u : RamState) : (do
      let x ← (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rdi.read u), u) :=
    (specM_bind_run _ _ (rdi_run u)).trans (hslice _ u)
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    rw [specM_bind_run _ _ hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hrsi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hds, hes]
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hdfRun _ (by simp [Operand.write, dataAccess]))).trans ?_
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (hrsi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [movsSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide), ofInt_div8]

theorem mov_string_operation_seg [Bindings] (t : RamState) (h : DataReady t) (hmode : In64BitMode t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = true) (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : (segBase ctx.segment + rsi.read t).toNat + n / 8 ≤ 2^32)
    (hdst : (rdi.read t).toNat + n / 8 ≤ 2^32)
    (hsrcMem : ∀ i, i < n / 8 →
      (t.external[segBase ctx.segment + rsi.read t + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < n / 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.Operations.MOV_STRING 64 n ctx).run t =
      (.ok (), movsSegSpec (segBase ctx.segment) n t) := by
  have hread := logicalMemRead_run_seg t h ctx.segment (rsi.read t) _ (hsr.access _) n hn
    .Memory_Read (.inl rfl) hsrc hsrcMem
  have hu : DataReady (dataAccess t "load") := h.dataAccess _
  have hwrite := logicalMemWrite_run (dataAccess t "load") hu false (rdi.read t) n hn
    ((Operand.mem (segBase ctx.segment + rsi.read t) : Operand n).read t) hdst hdstMem
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 0, u) := by
    change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
    rw [hu, show BitVec.extractLsb' 10 1 t.RFLAGS = dfBit t.RFLAGS from rfl, hdf]
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok ctx.segment :=
    fun seg => getEffectiveSegment_run_of_seg ctx seg hseg
  unfold X86.Instructions.Operations.MOV_STRING
  simp only [hges]
  have hg (u : RamState) : (get : X86.Runtime.SpecM X86.Exception RamState RamState).run u =
      (.ok u, u) := rfl
  have hslice (x : BitVec 64) (u : RamState) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hadd (x : BitVec 64) (k : Int) (u : RamState) :
      (liftM (Std.Bits.Add_int (n := 64) x k) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u =
        (.ok (x + BitVec.ofInt 64 k), u) := rfl
  have hrsi (u : RamState) : (do
      let x ← (RSI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rsi.read u), u) :=
    (specM_bind_run _ _ (rsi_run u)).trans (hslice _ u)
  have hrdi (u : RamState) : (do
      let x ← (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rdi.read u), u) :=
    (specM_bind_run _ _ (rdi_run u)).trans (hslice _ u)
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    rw [specM_bind_run _ _ hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hrsi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hes]
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hdfRun _ (by simp [Operand.write, dataAccess]))).trans ?_
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (hrsi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [movsSegSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide), ofInt_div8]

theorem mov_string_operation_down [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : (rsi.read t).toNat + n / 8 ≤ 2^32)
    (hdst : (rdi.read t).toNat + n / 8 ≤ 2^32)
    (hsrcMem : ∀ i, i < n / 8 → (t.external[rsi.read t + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < n / 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.Operations.MOV_STRING 64 n ctx).run t = (.ok (), movsDownSpec n t) := by
  have hread := logicalMemRead_run t h false (rsi.read t) n hn .Memory_Read (.inl rfl)
    hsrc hsrcMem
  have hu : DataReady (dataAccess t "load") := h.dataAccess _
  have hwrite := logicalMemWrite_run (dataAccess t "load") hu false (rdi.read t) n hn
    ((Operand.mem (rsi.read t) : Operand n).read t) hdst hdstMem
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 1, u) := by
    change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
    rw [hu, show BitVec.extractLsb' 10 1 t.RFLAGS = dfBit t.RFLAGS from rfl, hdf]
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  unfold X86.Instructions.Operations.MOV_STRING
  simp only [hges]
  have hg (u : RamState) : (get : X86.Runtime.SpecM X86.Exception RamState RamState).run u =
      (.ok u, u) := rfl
  have hslice (x : BitVec 64) (u : RamState) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hadd (x : BitVec 64) (k : Int) (u : RamState) :
      (liftM (Std.Bits.Add_int (n := 64) x k) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u =
        (.ok (x + BitVec.ofInt 64 k), u) := rfl
  have hrsi (u : RamState) : (do
      let x ← (RSI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rsi.read u), u) :=
    (specM_bind_run _ _ (rsi_run u)).trans (hslice _ u)
  have hrdi (u : RamState) : (do
      let x ← (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rdi.read u), u) :=
    (specM_bind_run _ _ (rdi_run u)).trans (hslice _ u)
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    rw [specM_bind_run _ _ hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hrsi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hds, hes]
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hdfRun _ (by simp [Operand.write, dataAccess]))).trans ?_
    simp (config := { decide := true }) only [↓reduceIte]
    refine (specM_bind_run _ _ (hrsi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [movsDownSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide), ofInt_neg_div8,
      ← BitVec.sub_eq_add_neg]

theorem mov_string_operation_down_seg [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t)
    (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = true) (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : (segBase ctx.segment + rsi.read t).toNat + n / 8 ≤ 2^32)
    (hdst : (rdi.read t).toNat + n / 8 ≤ 2^32)
    (hsrcMem : ∀ i, i < n / 8 →
      (t.external[segBase ctx.segment + rsi.read t + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < n / 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.Operations.MOV_STRING 64 n ctx).run t =
      (.ok (), movsDownSegSpec (segBase ctx.segment) n t) := by
  have hread := logicalMemRead_run_seg t h ctx.segment (rsi.read t) _ (hsr.access _) n hn
    .Memory_Read (.inl rfl) hsrc hsrcMem
  have hu : DataReady (dataAccess t "load") := h.dataAccess _
  have hwrite := logicalMemWrite_run (dataAccess t "load") hu false (rdi.read t) n hn
    ((Operand.mem (segBase ctx.segment + rsi.read t) : Operand n).read t) hdst hdstMem
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 1, u) := by
    change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
    rw [hu, show BitVec.extractLsb' 10 1 t.RFLAGS = dfBit t.RFLAGS from rfl, hdf]
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok ctx.segment :=
    fun seg => getEffectiveSegment_run_of_seg ctx seg hseg
  unfold X86.Instructions.Operations.MOV_STRING
  simp only [hges]
  have hg (u : RamState) : (get : X86.Runtime.SpecM X86.Exception RamState RamState).run u =
      (.ok u, u) := rfl
  have hslice (x : BitVec 64) (u : RamState) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hadd (x : BitVec 64) (k : Int) (u : RamState) :
      (liftM (Std.Bits.Add_int (n := 64) x k) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u =
        (.ok (x + BitVec.ofInt 64 k), u) := rfl
  have hrsi (u : RamState) : (do
      let x ← (RSI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rsi.read u), u) :=
    (specM_bind_run _ _ (rsi_run u)).trans (hslice _ u)
  have hrdi (u : RamState) : (do
      let x ← (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
      X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rdi.read u), u) :=
    (specM_bind_run _ _ (rdi_run u)).trans (hslice _ u)
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    rw [specM_bind_run _ _ hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (hg t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hrsi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    rw [hes]
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hdfRun _ (by simp [Operand.write, dataAccess]))).trans ?_
    simp (config := { decide := true }) only [↓reduceIte]
    refine (specM_bind_run _ _ (hrsi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (hrdi _)).trans ?_
    refine (specM_bind_run _ _ (hadd _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [movsDownSegSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide), ofInt_neg_div8,
      ← BitVec.sub_eq_add_neg]

theorem mov_string_operation_a32 [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (ctx : Instruction_Context)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : (rsi.read t).toNat + n / 8 < 2^32)
    (hdst : (rdi.read t).toNat + n / 8 < 2^32)
    (hsrcMem : ∀ i, i < n / 8 → (t.external[rsi.read t + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < n / 8 → (t.external[rdi.read t + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.Operations.MOV_STRING 32 n ctx).run t = (.ok (), movsSpec n t) := by
  have hread := logicalMemRead_run t h false (rsi.read t) n hn .Memory_Read (.inl rfl)
    (by omega) hsrcMem
  have hu : DataReady (dataAccess t "load") := h.dataAccess _
  have hwrite := logicalMemWrite_run (dataAccess t "load") hu false (rdi.read t) n hn
    ((Operand.mem (rsi.read t) : Operand n).read t) (by omega) hdstMem
  have hdfRun (u : RamState) (hu : u.RFLAGS = t.RFLAGS) :
      (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 0, u) := by
    change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
    rw [hu, show BitVec.extractLsb' 10 1 t.RFLAGS = dfBit t.RFLAGS from rfl, hdf]
  have hges : ∀ seg, Get_Effective_Segment ctx seg = .ok (nullDataSegment seg) :=
    fun seg => getEffectiveSegment_run ctx seg hseg hm64
  have has : ((rsi.read t).setWidth 32).setWidth 64 = rsi.read t :=
    setWidth32_setWidth64_of_lt (by omega)
  have had : ((rdi.read t).setWidth 32).setWidth 64 = rdi.read t :=
    setWidth32_setWidth64_of_lt (by omega)
  unfold X86.Instructions.Operations.MOV_STRING
  simp only [hges]
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    rw [specM_bind_run _ _ hmode]
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rsiSlice32_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend32_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice32_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend32_run _ _)).trans ?_
    rw [has, had, hds, hes]
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (hdfRun _ (by simp [Operand.write, dataAccess]))).trans ?_
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (rsiSlice32_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt32_run _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRSI32_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rdiSlice32_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt32_run _ _ _)).trans ?_
    refine (writeRDI32_run _ _).trans ?_
    simp only [movsSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess,
      Operand.read_write_reg_of_ne _ (show (6 : BitVec 5) ≠ 7 by decide), ofInt32_div8]
    rw [setWidth64_add_of_lt (by omega), setWidth64_add_of_lt (by omega)]

end X86Proofs
