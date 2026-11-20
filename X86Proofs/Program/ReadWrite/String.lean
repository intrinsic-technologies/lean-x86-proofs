import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Program.Compose

/-!
# String instructions: RSI, RDI, RCX, the direction flag, frames and preconditions

Shared by the string instructions (`MOVS`, `STOS`, `LODS`, `SCAS`, `CMPS` and their `REP` forms),
all with 64-bit addresses (no `67` prefix), flat segments and the direction flag clear (DF = 0,
`DirectionFlagClear`) or, for the `_down` forms, set (DF = 1, `DirectionFlagSet`): no string
effect writes DF, and every frame without `.df` keeps it (`AgreesExcept.directionFlagClear`), so a
program that clears it once keeps it clear until a CLD, STD or POPF.

- the reads and writes of `rsi`, `rdi`, `rcx` (`Core/Operand.lean`) as lean-x86 runs them (`rsiSlice_run`,
  `rdiSlice_run`, `rcxSlice_run`: the register read and its 64-bit slice), the direction flag read
  (`directionFlag_run`, `directionFlagSet_run`) and the address increment (`addInt64_run`;
  `ofInt_neg_div8` with DF = 1); the repeat stride binding (`getRepeatStringStride_run`);
  `writeRCX32_run`: a 32-bit count written back (ECX, as LOOP at address size 32 does).
- Frames built from the pieces of a string operation's state: register and memory writes,
  `dataAccess`, `setFlags`, `Next_IP`, and the step around a form (`AgreesExcept.write_reg`,
  `AgreesExcept.write_mem`, `AgreesExcept.of_dataAccess`, `AgreesExcept.of_setFlags`,
  `AgreesExcept.of_nextIP`, `AgreesExcept.of_afterStep`), chained with `AgreesExcept.trans`.
- The preconditions of the one-iteration triples: `MovsPre`, `StosPre`, `LodsPre`, `ScasPre`,
  `CmpsPre`; with an FS/GS override of the source DS:RSI (read at the segment's base plus RSI;
  ES:RDI takes no override): `MovsSegPre`, `LodsSegPre`, `CmpsSegPre`; with DF = 1, the same
  with `Down` (`MovsDownPre`, …, `CmpsDownSegPre`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem rsi_run (u : RamState) :
    (RSI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok (rsi.read u), u) := by
  simp [RSI, gprGet_eq, x86_runtime, Operand.read]
  rfl

theorem rdi_run (u : RamState) :
    (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok (rdi.read u), u) := by
  simp [RDI, gprGet_eq, x86_runtime, Operand.read]
  rfl

theorem writeRSI64_run (u : RamState) (v : BitVec 64) :
    (Write_RSI (size := 64) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), rsi.write u v) := by
  unfold Write_RSI
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rsi_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError, mergeGPR64_run, mergeGPR_64,
    RSI_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp [Operand.write_reg64, gprIndex]
  rfl

theorem writeRDI64_run (u : RamState) (v : BitVec 64) :
    (Write_RDI (size := 64) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), rdi.write u v) := by
  unfold Write_RDI
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rdi_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError, mergeGPR64_run, mergeGPR_64,
    RDI_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp [Operand.write_reg64, gprIndex]
  rfl

theorem zeroExtend64_run (x : BitVec 64) (u : RamState) :
    (Std.Bits.Zero_Extend (source_size := 64) x 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
  simp [x86_runtime]

theorem ofInt_div8 (n : Nat) : BitVec.ofInt 64 ((n : Int) / 8) = BitVec.ofNat 64 (n / 8) := by
  rw [show (n : Int) / 8 = ((n / 8 : Nat) : Int) by omega, BitVec.ofInt_natCast]

/-- `BitVec.ofInt` of a negated byte count: the negated address step. -/
theorem ofInt_neg_div8 (n : Nat) :
    BitVec.ofInt 64 (-((n : Int) / 8)) = -BitVec.ofNat 64 (n / 8) := by
  rw [show -((n : Int) / 8) = -((n / 8 : Nat) : Int) by omega, BitVec.ofInt_neg,
    BitVec.ofInt_natCast]

theorem rcx_run (u : RamState) :
    (RCX : X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok (rcx.read u), u) := by
  simp [RCX, gprGet_eq, x86_runtime, Operand.read]
  rfl

theorem writeRCX64_run (u : RamState) (v : BitVec 64) :
    (Write_RCX (size := 64) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), rcx.write u v) := by
  unfold Write_RCX
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rcx_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError, mergeGPR64_run, mergeGPR_64,
    RCX_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp [Operand.write_reg64, gprIndex]
  rfl

/-- `Write_RCX` at 32 bits (a count at address size 32): ECX := `v`, the upper half of RCX
cleared. -/
theorem writeRCX32_run (u : RamState) (v : BitVec 32) :
    (Write_RCX (size := 32) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), rcx.write u (v.setWidth 64)) := by
  unfold Write_RCX
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rcx_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError, mergeGPR_run 32 (by decide), mergeGPR_32,
    RCX_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp [Operand.write_reg64, gprIndex]
  rfl

theorem rcx_read_write (u : RamState) (v : BitVec 64) : rcx.read (rcx.write u v) = v := by
  simp

/-- `Write_RSI` at 32 bits (address size 32): ESI := `v`, the upper half of RSI cleared. -/
theorem writeRSI32_run (u : RamState) (v : BitVec 32) :
    (Write_RSI (size := 32) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), rsi.write u (v.setWidth 64)) := by
  unfold Write_RSI
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rsi_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError, mergeGPR_run 32 (by decide), mergeGPR_32,
    RSI_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp [Operand.write_reg64, gprIndex]
  rfl

/-- `Write_RDI` at 32 bits (address size 32): EDI := `v`, the upper half of RDI cleared. -/
theorem writeRDI32_run (u : RamState) (v : BitVec 32) :
    (Write_RDI (size := 32) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), rdi.write u (v.setWidth 64)) := by
  unfold Write_RDI
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rdi_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError, mergeGPR_run 32 (by decide), mergeGPR_32,
    RDI_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp [Operand.write_reg64, gprIndex]
  rfl

/-- The stride binding answers 1 for a positive count. -/
theorem getRepeatStringStride_run [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (u : RamState) (size count : Int) (hpos : 0 < count) :
    (Get_Repeat_String_Stride size count : X86.Runtime.SpecM X86.Exception RamState Int).run u =
      (.ok 1, u) := by
  unfold Get_Repeat_String_Stride
  rw [specM_bind_run _ _ (show (get : X86.Runtime.SpecM X86.Exception RamState RamState).run u =
    (.ok u, u) from rfl)]
  apply specM_liftNoSourceException_run
  have := hstride u size count hpos
  erw [this]
  rfl

/-! ### lean-x86's reads of the string registers and the direction flag -/

/-- The 64-bit slice of a 64-bit value is the value. -/
theorem checkedSliceRead64_run (x : BitVec 64) (u : RamState) :
    (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok x, u) := by
  simp [X86.Runtime.CheckedSlice.read, x86_runtime]

/-- RSI read at address size 64, as the string operations read it (the register, then its
64-bit slice). -/
theorem rsiSlice_run (u : RamState) : (do
    let x ← (RSI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
    X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rsi.read u), u) :=
  (specM_bind_run _ _ (rsi_run u)).trans (checkedSliceRead64_run _ u)

/-- RDI read at address size 64 (`rsiSlice_run` for RDI). -/
theorem rdiSlice_run (u : RamState) : (do
    let x ← (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
    X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rdi.read u), u) :=
  (specM_bind_run _ _ (rdi_run u)).trans (checkedSliceRead64_run _ u)

/-- RCX read at address size 64 (`rsiSlice_run` for RCX). -/
theorem rcxSlice_run (u : RamState) : (do
    let x ← (RCX : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
    X86.Runtime.CheckedSlice.read x 0 64).run u = (.ok (rcx.read u), u) :=
  (specM_bind_run _ _ (rcx_run u)).trans (checkedSliceRead64_run _ u)

/-! ### Address size 32 (`67`): ESI, EDI, ECX

With an address-size prefix the string operations read the low 32 bits of RSI, RDI and RCX
(zero-extended as addresses) and write them back as 32-bit values (the upper halves cleared). The
`_a32` lemmas below take those registers below 4 GiB and the increments without a 32-bit wrap, so
the reads and writes are those of address size 64 (`setWidth32_setWidth64_of_lt`,
`setWidth64_add_of_lt`). -/

/-- The 32-bit slice of a 64-bit value (RSI, RDI, RCX at address size 32). -/
theorem checkedSliceRead32_run (x : BitVec 64) (u : RamState) :
    (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run u = (.ok (x.setWidth 32), u) := by
  simp [X86.Runtime.CheckedSlice.read, x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk,
    StateT.pure, BitVec.setWidth_eq_extractLsb']

/-- RSI read at address size 32: ESI. -/
theorem rsiSlice32_run (u : RamState) : (do
    let x ← (RSI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
    X86.Runtime.CheckedSlice.read x 0 32).run u = (.ok ((rsi.read u).setWidth 32), u) :=
  (specM_bind_run _ _ (rsi_run u)).trans (checkedSliceRead32_run _ u)

/-- RDI read at address size 32: EDI. -/
theorem rdiSlice32_run (u : RamState) : (do
    let x ← (RDI : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
    X86.Runtime.CheckedSlice.read x 0 32).run u = (.ok ((rdi.read u).setWidth 32), u) :=
  (specM_bind_run _ _ (rdi_run u)).trans (checkedSliceRead32_run _ u)

/-- RCX read at address size 32: ECX. -/
theorem rcxSlice32_run (u : RamState) : (do
    let x ← (RCX : X86.Runtime.SpecM X86.Exception RamState (BitVec 64))
    X86.Runtime.CheckedSlice.read x 0 32).run u = (.ok ((rcx.read u).setWidth 32), u) :=
  (specM_bind_run _ _ (rcx_run u)).trans (checkedSliceRead32_run _ u)

/-- A 32-bit address zero-extended to 64 bits. -/
theorem zeroExtend32_run (x : BitVec 32) (u : RamState) :
    (Std.Bits.Zero_Extend (source_size := 32) x 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok (x.setWidth 64), u) := by
  simp [x86_runtime]

/-- The 32-bit address increment: `x + k` (wrapping at 32 bits). -/
theorem addInt32_run (x : BitVec 32) (k : Int) (u : RamState) :
    (liftM (Std.Bits.Add_int (n := 32) x k) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run u =
      (.ok (x + BitVec.ofInt 32 k), u) := rfl

/-- A value below 4 GiB is its low 32 bits, zero-extended. -/
theorem setWidth32_setWidth64_of_lt {x : BitVec 64} (h : x.toNat < 2^32) :
    (x.setWidth 32).setWidth 64 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- A 32-bit increment of the low 32 bits of `x`, zero-extended, is the 64-bit increment of `x`
when it does not wrap. -/
theorem setWidth64_add_of_lt {x : BitVec 64} {k : Nat} (h : x.toNat + k < 2^32) :
    (x.setWidth 32 + BitVec.ofNat 32 k).setWidth 64 = x + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ofInt32_div8 (n : Nat) : BitVec.ofInt 32 ((n : Int) / 8) = BitVec.ofNat 32 (n / 8) := by
  rw [show (n : Int) / 8 = ((n / 8 : Nat) : Int) by omega, BitVec.ofInt_natCast]

/-- ECX - 1, zero-extended, is RCX - 1 for RCX ≠ 0 below 4 GiB. -/
theorem setWidth64_sub_one_of_lt {x : BitVec 64} (h : x.toNat < 2^32) (h0 : x ≠ 0) :
    (x.setWidth 32 - 1).setWidth 64 = x - 1 := by
  have h0' : x.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simpa using e))
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  have h2 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, h1, h2]
  rw [Nat.mod_eq_of_lt (show x.toNat < 2^32 by omega)]
  omega

/-- RCX - 1 stays below 4 GiB for RCX ≠ 0 below 4 GiB. -/
theorem toNat_sub_one_lt_of_lt {x : BitVec 64} (h : x.toNat < 2^32) (h0 : x ≠ 0) :
    (x - 1).toNat < 2^32 := by
  rw [← setWidth64_sub_one_of_lt h h0, BitVec.toNat_setWidth]
  have := (x.setWidth 32 - 1).isLt
  omega

/-- ECX zero-extended is RCX below 4 GiB, so ECX tests zero as RCX does. -/
theorem setWidth32_beq_zero_of_lt {x : BitVec 64} (h : x.toNat < 2^32) :
    (x.setWidth 32 == 0#32) = (x == 0#64) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro he
    rw [← setWidth32_setWidth64_of_lt h, he]
    rfl
  · rintro rfl
    rfl

/-- With the direction flag clear, lean-x86's `RFLAGS.DF` reads 0. -/
theorem directionFlag_run (u : RamState) (hdf : DirectionFlagClear u.RFLAGS) :
    (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 0, u) := by
  change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
  rw [show BitVec.extractLsb' 10 1 u.RFLAGS = 0 from hdf]

/-- With the direction flag set, lean-x86's `RFLAGS.DF` reads 1. -/
theorem directionFlagSet_run (u : RamState) (hdf : DirectionFlagSet u.RFLAGS) :
    (X86.RFLAGS.DF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u = (.ok 1, u) := by
  change (Except.ok (BitVec.extractLsb' 10 1 u.RFLAGS), u) = _
  rw [show BitVec.extractLsb' 10 1 u.RFLAGS = 1 from hdf]

/-- Setting the status flags changes no operand. -/
@[simp] theorem Operand.read_setFlags {n : Nat} (s : RamState) (f : StatusFlags) (op : Operand n) :
    op.read (setFlags s f) = op.read s := by
  have hd : dfBit (setFlags s f).RFLAGS = dfBit s.RFLAGS := dfBit_store f s.RFLAGS
  exact Operand.read_of_eq (s := setFlags s f) (t := s) rfl rfl rfl rfl hd rfl rfl rfl rfl rfl
    op

/-- Storing status flags keeps the direction flag. -/
theorem DirectionFlagClear.store {r : BitVec 64} (h : DirectionFlagClear r) (f : StatusFlags) :
    DirectionFlagClear (f.store r) := by
  unfold DirectionFlagClear dfBit at *
  rw [← extractLsb'_clearStatusFlags _ 10 (by decide) (by decide), clearStatusFlags_store,
    extractLsb'_clearStatusFlags _ 10 (by decide) (by decide), h]

/-- Storing status flags keeps the direction flag set. -/
theorem DirectionFlagSet.store {r : BitVec 64} (h : DirectionFlagSet r) (f : StatusFlags) :
    DirectionFlagSet (f.store r) := by
  unfold DirectionFlagSet dfBit at *
  rw [← extractLsb'_clearStatusFlags _ 10 (by decide) (by decide), clearStatusFlags_store,
    extractLsb'_clearStatusFlags _ 10 (by decide) (by decide), h]

/-- The 64-bit address increment: `x + k` (wrapping). -/
theorem addInt64_run (x : BitVec 64) (k : Int) (u : RamState) :
    (liftM (Std.Bits.Add_int (n := 64) x k) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u =
      (.ok (x + BitVec.ofInt 64 k), u) := rfl

/-! ### Frames of the pieces of a string operation -/

/-- Writing register `r` (at any size) changes only `r`. -/
theorem AgreesExcept.write_reg {n : Nat} (t : RamState) (r : BitVec 5) (v : BitVec n) :
    AgreesExcept [.reg r] t ((Operand.reg r : Operand n).write t v) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r' =>
      have hne : r ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
      have := Operand.read_write_reg_of_ne (m := 64) t hne v
      simp only [Operand.read_reg64] at this
      exact this
    | flags => rfl
    | rip => rfl
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · simp only [fixedPart, Operand.write, beforeFetch, resetStepFields]

/-- Writing `n` bits of memory at `a` changes only those `n / 8` bytes. -/
theorem AgreesExcept.write_mem {n : Nat} (t : RamState) (a : BitVec 64) (v : BitVec n) :
    AgreesExcept [.mem a (n / 8)] t ((Operand.mem a : Operand n).write t v) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r => rfl
    | flags => rfl
    | rip => rfl
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem a (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, Operand.write, beforeFetch, resetStepFields]
  · exact memStore_isSome _ _ _ x hx

/-- A data access's bookkeeping (`dataAccess`) changes nothing an effect lists. -/
theorem AgreesExcept.of_dataAccess (t : RamState) (event : String) :
    AgreesExcept [] t (dataAccess t event) := by
  refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · simp only [fixedPart, X86Proofs.dataAccess, beforeFetch, resetStepFields]

/-- Setting the status flags changes only the flags. -/
theorem AgreesExcept.of_setFlags (t : RamState) (f : StatusFlags) :
    AgreesExcept [.flags] t (setFlags t f) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | flags => exact absurd (by simp) hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | df => exact dfBit_store _ _
    | _ => rfl
  · simp only [fixedPart, X86Proofs.setFlags, beforeFetch, resetStepFields, clearStatusFlags_store]

/-- Setting `Next_IP` changes nothing an effect lists. -/
theorem AgreesExcept.of_nextIP (t : RamState) (ip : BitVec 64) :
    AgreesExcept [] t { t with Next_IP := ip } := by
  refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · simp only [fixedPart, beforeFetch, resetStepFields]

/-- A step whose form changes only `cs` (from the state the form starts in) changes only `cs` and
RIP. -/
theorem AgreesExcept.of_afterStep {cs : List Component} (s : RamState) (length : Nat)
    (form : RamState → RamState)
    (h : AgreesExcept cs (afterFetches (beforeFetch s) (length + 1))
      (form (afterFetches (beforeFetch s) (length + 1)))) :
    AgreesExcept (cs ++ [.rip]) s (X86Proofs.afterStep s length form) := by
  have h0 : AgreesExcept [] s (afterFetches (beforeFetch s) (length + 1)) := by
    refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | mem a len => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | _ => rfl
    · simp only [fixedPart, afterFetches, beforeFetch, resetStepFields]
  have h1 : AgreesExcept [.rip] (form (afterFetches (beforeFetch s) (length + 1)))
      (X86Proofs.afterStep s length form) := by
    refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | rip => exact absurd (by simp) hc
      | mem a len => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | _ => rfl
    · simp only [fixedPart, X86Proofs.afterStep, finishStep, beforeFetch, resetStepFields]
  simpa using (h0.trans h).trans h1

/-! ### Preconditions of the one-iteration triples -/

/-- What `movs` of `len` bytes at `p` (an instruction of `codeLen` bytes) needs besides
`ReadyToStep`: RIP = `p`, the direction flag clear, the source (at RSI) readable, the destination
(at RDI) writable in place and apart from the instruction's bytes. -/
structure MovsPre (p : BitVec 64) (codeLen len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  read : MemReadable s (rsi.read s) len
  write : MemWritable s (rdi.read s) len
  code : RangeApart (rdi.read s) len p codeLen

/-- What `stos` of `len` bytes at `p` needs: RIP = `p`, the direction flag clear, the
destination (at RDI) writable in place and apart from the instruction's bytes. -/
structure StosPre (p : BitVec 64) (codeLen len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  write : MemWritable s (rdi.read s) len
  code : RangeApart (rdi.read s) len p codeLen

/-- What `lods` of `len` bytes at `p` needs: RIP = `p`, the direction flag clear, the source
(at RSI) readable. -/
structure LodsPre (p : BitVec 64) (len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  read : MemReadable s (rsi.read s) len

/-- What `scas` of `len` bytes at `p` needs: RIP = `p`, the direction flag clear, the operand
at RDI readable. -/
structure ScasPre (p : BitVec 64) (len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  read : MemReadable s (rdi.read s) len

/-- What `cmps` of `len` bytes at `p` needs: RIP = `p`, the direction flag clear, the operands
at RSI and RDI readable. -/
structure CmpsPre (p : BitVec 64) (len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  src : MemReadable s (rsi.read s) len
  dst : MemReadable s (rdi.read s) len

/-! ### Preconditions with an FS/GS segment override

The source DS:RSI of MOVS, LODS and CMPS takes a segment override (FS or GS, register `r`, base
`base`): it is read at `base + RSI`. The destination ES:RDI takes none, so STOS and SCAS are the
same with or without the prefix. -/

/-- `MovsPre` with the source at `base + RSI` through segment `r`, ready with base `base`. -/
structure MovsSegPre (p : BitVec 64) (codeLen len : Nat) (r : SegReg) (base : BitVec 64)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  read : MemReadable s (base + rsi.read s) len
  write : MemWritable s (rdi.read s) len
  code : RangeApart (rdi.read s) len p codeLen
  seg : r.Ready base s

/-- `LodsPre` with the source at `base + RSI` through segment `r`, ready with base `base`. -/
structure LodsSegPre (p : BitVec 64) (len : Nat) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  read : MemReadable s (base + rsi.read s) len
  seg : r.Ready base s

/-- `CmpsPre` with the first operand at `base + RSI` through segment `r`, ready with base
`base`. -/
structure CmpsSegPre (p : BitVec 64) (len : Nat) (r : SegReg) (base : BitVec 64) (s : RamState) :
    Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  src : MemReadable s (base + rsi.read s) len
  dst : MemReadable s (rdi.read s) len
  seg : r.Ready base s

/-! ### Preconditions with the direction flag set

The same as the preconditions above with DF = 1 (`DirectionFlagSet`): the `_down` forms of the
string family, which step RSI and RDI down. -/

/-- `MovsPre` with the direction flag set. -/
structure MovsDownPre (p : BitVec 64) (codeLen len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  read : MemReadable s (rsi.read s) len
  write : MemWritable s (rdi.read s) len
  code : RangeApart (rdi.read s) len p codeLen

/-- `StosPre` with the direction flag set. -/
structure StosDownPre (p : BitVec 64) (codeLen len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  write : MemWritable s (rdi.read s) len
  code : RangeApart (rdi.read s) len p codeLen

/-- `LodsPre` with the direction flag set. -/
structure LodsDownPre (p : BitVec 64) (len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  read : MemReadable s (rsi.read s) len

/-- `ScasPre` with the direction flag set. -/
structure ScasDownPre (p : BitVec 64) (len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  read : MemReadable s (rdi.read s) len

/-- `CmpsPre` with the direction flag set. -/
structure CmpsDownPre (p : BitVec 64) (len : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  src : MemReadable s (rsi.read s) len
  dst : MemReadable s (rdi.read s) len

/-- `MovsSegPre` with the direction flag set. -/
structure MovsDownSegPre (p : BitVec 64) (codeLen len : Nat) (r : SegReg) (base : BitVec 64)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  read : MemReadable s (base + rsi.read s) len
  write : MemWritable s (rdi.read s) len
  code : RangeApart (rdi.read s) len p codeLen
  seg : r.Ready base s

/-- `LodsSegPre` with the direction flag set. -/
structure LodsDownSegPre (p : BitVec 64) (len : Nat) (r : SegReg) (base : BitVec 64)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  read : MemReadable s (base + rsi.read s) len
  seg : r.Ready base s

/-- `CmpsSegPre` with the direction flag set. -/
structure CmpsDownSegPre (p : BitVec 64) (len : Nat) (r : SegReg) (base : BitVec 64)
    (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagSet s.RFLAGS
  src : MemReadable s (base + rsi.read s) len
  dst : MemReadable s (rdi.read s) len
  seg : r.Ready base s

attribute [x86_compose] rcx

/-! ### Preconditions after a block -/

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre_simp] theorem directionFlagClear_iff (t : RamState) :
    DirectionFlagClear t.RFLAGS ↔ (Operand.df : Operand 1).read t = 0#1 := by
  simp [DirectionFlagClear, Operand.read, dfBit]

@[x86_pre_simp] theorem directionFlagSet_iff (t : RamState) :
    DirectionFlagSet t.RFLAGS ↔ (Operand.df : Operand 1).read t = 1#1 := by
  simp [DirectionFlagSet, Operand.read, dfBit]

theorem DirectionFlagClear.of_obs (ho : Obs (e.after s true) s')
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1) :
    DirectionFlagClear s'.RFLAGS := by
  rw [directionFlagClear_iff, Obs.back_df ho]
  exact hdf

theorem DirectionFlagSet.of_obs (ho : Obs (e.after s true) s')
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 1#1) :
    DirectionFlagSet s'.RFLAGS := by
  rw [directionFlagSet_iff, Obs.back_df ho]
  exact hdf

section StringCarry

variable (h : e.Holds s s') (ho : Obs (e.after s true) s') {p : BitVec 64} {codeLen len : Nat}
  {r : SegReg} {base : BitVec 64}
include h ho

theorem MemReadable.carry_reg {n : BitVec 5} {len : Nat}
    (hr : MemReadable s ((Operand.reg n : Operand 64).read (e.after s true)) len) :
    MemReadable s' ((Operand.reg n : Operand 64).read s') len := by
  rw [Obs.back_reg ho]; exact hr.of_holds h

theorem MemReadable.carry_seg {n : BitVec 5} {len : Nat} (base : BitVec 64)
    (hr : MemReadable s (base + (Operand.reg n : Operand 64).read (e.after s true)) len) :
    MemReadable s' (base + (Operand.reg n : Operand 64).read s') len := by
  rw [Obs.back_reg ho]; exact hr.of_holds h

theorem MemWritable.carry_reg {n : BitVec 5} {len : Nat}
    (hw : MemWritable s ((Operand.reg n : Operand 64).read (e.after s true)) len) :
    MemWritable s' ((Operand.reg n : Operand 64).read s') len := by
  rw [Obs.back_reg ho]; exact hw.of_holds h

omit h in
theorem RangeApart.carry_reg {n : BitVec 5} {len : Nat} {codeLen : Nat}
    (hap : RangeApart ((Operand.reg n : Operand 64).read (e.after s true)) len p codeLen) :
    RangeApart ((Operand.reg n : Operand 64).read s') len p codeLen := by
  rw [Obs.back_reg ho]; exact hap

end StringCarry

section Strings

variable (h : e.Holds s s') (ho : Obs (e.after s true) s') {p : BitVec 64} {codeLen len : Nat}
  {r : SegReg} {base : BitVec 64} (hrip : e.rip = p)
include h ho hrip

@[x86_pre] theorem MovsPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hr : MemReadable s (rsi.read (e.after s true)) len)
    (hw : MemWritable s (rdi.read (e.after s true)) len)
    (hap : RangeApart (rdi.read (e.after s true)) len p codeLen) : MovsPre p codeLen len s' :=
  ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, MemReadable.carry_reg h ho hr,
    MemWritable.carry_reg h ho hw, RangeApart.carry_reg ho hap⟩

@[x86_pre] theorem StosPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hw : MemWritable s (rdi.read (e.after s true)) len)
    (hap : RangeApart (rdi.read (e.after s true)) len p codeLen) : StosPre p codeLen len s' :=
  ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, MemWritable.carry_reg h ho hw,
    RangeApart.carry_reg ho hap⟩

@[x86_pre] theorem LodsPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hr : MemReadable s (rsi.read (e.after s true)) len) : LodsPre p len s' :=
  ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, MemReadable.carry_reg h ho hr⟩

@[x86_pre] theorem ScasPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hr : MemReadable s (rdi.read (e.after s true)) len) : ScasPre p len s' :=
  ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, MemReadable.carry_reg h ho hr⟩

@[x86_pre] theorem CmpsPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hsrc : MemReadable s (rsi.read (e.after s true)) len)
    (hdst : MemReadable s (rdi.read (e.after s true)) len) : CmpsPre p len s' :=
  ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, MemReadable.carry_reg h ho hsrc,
    MemReadable.carry_reg h ho hdst⟩

@[x86_pre] theorem MovsSegPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hr : MemReadable s (base + rsi.read (e.after s true)) len)
    (hw : MemWritable s (rdi.read (e.after s true)) len)
    (hap : RangeApart (rdi.read (e.after s true)) len p codeLen) (hseg : r.Ready base s) :
    MovsSegPre p codeLen len r base s' :=
  ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, MemReadable.carry_seg h ho base hr,
    MemWritable.carry_reg h ho hw, RangeApart.carry_reg ho hap, h.segReady_iff.mpr hseg⟩

@[x86_pre] theorem LodsSegPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hr : MemReadable s (base + rsi.read (e.after s true)) len) (hseg : r.Ready base s) :
    LodsSegPre p len r base s' :=
  ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, MemReadable.carry_seg h ho base hr,
    h.segReady_iff.mpr hseg⟩

@[x86_pre] theorem CmpsSegPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hsrc : MemReadable s (base + rsi.read (e.after s true)) len)
    (hdst : MemReadable s (rdi.read (e.after s true)) len) (hseg : r.Ready base s) :
    CmpsSegPre p len r base s' :=
  ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, MemReadable.carry_seg h ho base hsrc,
    MemReadable.carry_reg h ho hdst, h.segReady_iff.mpr hseg⟩

@[x86_pre] theorem MovsDownPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 1#1)
    (hr : MemReadable s (rsi.read (e.after s true)) len)
    (hw : MemWritable s (rdi.read (e.after s true)) len)
    (hap : RangeApart (rdi.read (e.after s true)) len p codeLen) :
    MovsDownPre p codeLen len s' :=
  ⟨h.rip_of hrip, DirectionFlagSet.of_obs ho hdf, MemReadable.carry_reg h ho hr,
    MemWritable.carry_reg h ho hw, RangeApart.carry_reg ho hap⟩

@[x86_pre] theorem StosDownPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 1#1)
    (hw : MemWritable s (rdi.read (e.after s true)) len)
    (hap : RangeApart (rdi.read (e.after s true)) len p codeLen) :
    StosDownPre p codeLen len s' :=
  ⟨h.rip_of hrip, DirectionFlagSet.of_obs ho hdf, MemWritable.carry_reg h ho hw,
    RangeApart.carry_reg ho hap⟩

@[x86_pre] theorem LodsDownPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 1#1)
    (hr : MemReadable s (rsi.read (e.after s true)) len) : LodsDownPre p len s' :=
  ⟨h.rip_of hrip, DirectionFlagSet.of_obs ho hdf, MemReadable.carry_reg h ho hr⟩

@[x86_pre] theorem ScasDownPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 1#1)
    (hr : MemReadable s (rdi.read (e.after s true)) len) : ScasDownPre p len s' :=
  ⟨h.rip_of hrip, DirectionFlagSet.of_obs ho hdf, MemReadable.carry_reg h ho hr⟩

@[x86_pre] theorem CmpsDownPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 1#1)
    (hsrc : MemReadable s (rsi.read (e.after s true)) len)
    (hdst : MemReadable s (rdi.read (e.after s true)) len) : CmpsDownPre p len s' :=
  ⟨h.rip_of hrip, DirectionFlagSet.of_obs ho hdf, MemReadable.carry_reg h ho hsrc,
    MemReadable.carry_reg h ho hdst⟩

@[x86_pre] theorem MovsDownSegPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 1#1)
    (hr : MemReadable s (base + rsi.read (e.after s true)) len)
    (hw : MemWritable s (rdi.read (e.after s true)) len)
    (hap : RangeApart (rdi.read (e.after s true)) len p codeLen) (hseg : r.Ready base s) :
    MovsDownSegPre p codeLen len r base s' :=
  ⟨h.rip_of hrip, DirectionFlagSet.of_obs ho hdf, MemReadable.carry_seg h ho base hr,
    MemWritable.carry_reg h ho hw, RangeApart.carry_reg ho hap, h.segReady_iff.mpr hseg⟩

@[x86_pre] theorem LodsDownSegPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 1#1)
    (hr : MemReadable s (base + rsi.read (e.after s true)) len) (hseg : r.Ready base s) :
    LodsDownSegPre p len r base s' :=
  ⟨h.rip_of hrip, DirectionFlagSet.of_obs ho hdf, MemReadable.carry_seg h ho base hr,
    h.segReady_iff.mpr hseg⟩

@[x86_pre] theorem CmpsDownSegPre.of_holds
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 1#1)
    (hsrc : MemReadable s (base + rsi.read (e.after s true)) len)
    (hdst : MemReadable s (rdi.read (e.after s true)) len) (hseg : r.Ready base s) :
    CmpsDownSegPre p len r base s' :=
  ⟨h.rip_of hrip, DirectionFlagSet.of_obs ho hdf, MemReadable.carry_seg h ho base hsrc,
    MemReadable.carry_reg h ho hdst, h.segReady_iff.mpr hseg⟩

end Strings

end Carry

end X86Proofs
