import X86Proofs.Core.X87Arith
import X86.Instructions.F2XM1
import X86.Instructions.FSIN
import X86.Instructions.FCOS
import X86.Instructions.FPTAN
import X86.Instructions.FSINCOS
import X86.Instructions.FPATAN
import X86.Instructions.FYL2X
import X86.Instructions.FYL2XP1

/-!
# x87 transcendentals: lean-x86's numerical bindings at a control word

F2XM1, FSIN, FCOS, FPTAN, FSINCOS, FPATAN, FYL2X and FYL2XP1 compute with lean-x86's helpers
(`FP87.Power2Minus_One`, `FP87.Sin`, `FP87.Cos`, `FP87.Tan`, `FP87.Sin_Cos`, `FP87.Atan`,
`FP87.Log2_Multiply`, `FP87.Log2_Add_Multiply`), which classify the operands and send the finite
ones to the machine's numerical bindings (`Emulate_F2XM1`, `Emulate_FSIN`, …), opaque functions
that may read the whole state and may diverge. As for RCPSS (`fpRcp`, `Core/Float.lean`), the
library states them relative to the binding: `x87BindVal m fcw` is what the helper `m` returns
from a state whose control word is `fcw`, and `X87BindOk m fcw` says that it returns that value,
the same from every state with control word `fcw`, and leaves the state alone (the binding depends
on the operands and the control word only, and the helper takes no `UNSPECIFIED` branch). The
triples take it as a precondition.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

/-- `Bit b`: 1 if `b`, else 0. -/
theorem bit_eq (b : Bool) : Helpers.Bit b = .ok (if b = true then 1 else 0) := by
  cases b <;> rfl

/-- The bit `lo` of `setSlice x lo 1 v` is `v`. -/
theorem extractLsb'_setSlice_one {n : Nat} (x : BitVec n) (lo : Nat) (v : BitVec 1) (h : lo < n) :
    (setSlice x lo 1 v).extractLsb' lo 1 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega : i = 0) with rfl
  simp [getLsbD_setSlice _ _ _ _ _ h]

/-- Bit `k` of `setSlice x lo 1 v` is bit `k` of `x` for `k ≠ lo`. -/
theorem extractLsb'_setSlice_one_ne {n : Nat} (x : BitVec n) (lo k : Nat) (v : BitVec 1)
    (h : k < n) (hne : lo ≠ k) : (setSlice x lo 1 v).extractLsb' k 1 = x.extractLsb' k 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega : i = 0) with rfl
  simp [getLsbD_setSlice _ _ _ _ _ h]
  omega

/-- What the helper `m` returns from a state whose control word is `fcw` (the rest lean-x86's
default state). -/
def x87BindRun {α : Type} (m : PartialSpecM X86.Exception RamState α) (fcw : BitVec 16) :
    Option (Except (Error X86.Exception) α) :=
  (m.run (fcwState fcw)).map Prod.fst

/-- The value the helper `m` returns at control word `fcw` (`default` if it fails or diverges). -/
def x87BindVal {α : Type} [Inhabited α] (m : PartialSpecM X86.Exception RamState α)
    (fcw : BitVec 16) : α :=
  match x87BindRun m fcw with
  | some (.ok v) => v
  | _ => default

/-- `m` returns a value, the same from every state with control word `fcw`, and leaves the state
alone. -/
def X87BindOk {α : Type} (m : PartialSpecM X86.Exception RamState α) (fcw : BitVec 16) : Prop :=
  ∃ v, ∀ s : RamState, s.FP87_Control = fcw → m.run s = some (.ok v, s)

theorem X87BindOk.run {α : Type} [Inhabited α] {m : PartialSpecM X86.Exception RamState α}
    {s : RamState} (h : X87BindOk m s.FP87_Control) :
    m.run s = some (.ok (x87BindVal m s.FP87_Control), s) := by
  obtain ⟨v, hv⟩ := h
  have h1 := hv (fcwState s.FP87_Control) rfl
  have hval : x87BindVal m s.FP87_Control = v := by
    unfold x87BindVal x87BindRun
    rw [h1]
    rfl
  rw [hval]
  exact hv s rfl

/-- `X87BindOk.run` for a total helper (`FP87.Scale`), stated on its lift. -/
theorem X87BindOk.run_total {α : Type} [Inhabited α] {m : SpecM X86.Exception RamState α}
    {s : RamState} (h : X87BindOk (liftTotal m) s.FP87_Control) :
    m.run s = (.ok (x87BindVal (liftTotal m) s.FP87_Control), s) :=
  Option.some.inj h.run

/-- The status word FPATAN's operation leaves: C0, C2, C3 the oracle's next three bits, C1 :=
whether the result was rounded up, the flags `ex` ORed in, as lean-x86 sets them. -/
def x87PatanFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool) (ex : BitVec 6) :
    BitVec 16 :=
  fswOrFlags (setSlice (setSlice (setSlice (setSlice (setSlice fsw 8 1
    (BitVec.ofBool (oracleBit o))) 9 1 0) 10 1 (BitVec.ofBool (oracleBit (oracleSkip o 1)))) 14 1
    (BitVec.ofBool (oracleBit (oracleSkip (oracleSkip o 1) 1)))) 9 1 (if up = true then 1 else 0))
    ex

theorem x87PatanFsw_eq (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool) (ex : BitVec 6) :
    x87PatanFsw fsw o up ex =
      fswSetC (fswOrFlags fsw ex) (oBit o 0) (if up = true then 1 else 0) (oBit o 1)
        (oBit o 2) := by
  simp only [x87PatanFsw, oBit, oracleSkip_oracleSkip, oracleSkip_zero]
  fsw_bits
  all_goals cases up <;> simp [getElem_setSlice]

@[simp] theorem fswTop_x87PatanFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswTop (x87PatanFsw fsw o up ex) = fswTop fsw := by
  simp [x87PatanFsw_eq]

@[simp] theorem fswES_x87PatanFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswES (x87PatanFsw fsw o up ex) = fswES fsw := by
  simp [x87PatanFsw_eq]

theorem fswRest_x87PatanFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswRest (x87PatanFsw fsw o up ex) = fswOrFlags (fswRest fsw) ex := by
  rw [x87PatanFsw_eq]
  fsw_bits

theorem fswCC_x87PatanFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up : Bool)
    (ex : BitVec 6) : fswCC (x87PatanFsw fsw o up ex) &&& 2 = ccC1 up := by
  rw [x87PatanFsw_eq, fswCC_fswSetC]
  generalize oBit o 0 = a
  generalize oBit o 1 = b
  generalize oBit o 2 = c
  revert a b c
  cases up <;> decide

/-- The status word FSIN, FCOS, FPTAN and FSINCOS leave: C0, C3 the oracle's next two bits, C1 :=
whether the result was rounded up, C2 := whether the operand was out of range, the flags `ex` ORed
in, as lean-x86 sets them. -/
def x87SinFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool) (ex : BitVec 6) :
    BitVec 16 :=
  fswOrFlags (setSlice (setSlice (setSlice (setSlice (setSlice (setSlice fsw 8 1
    (BitVec.ofBool (oracleBit o))) 9 1 0) 10 1 0) 14 1
    (BitVec.ofBool (oracleBit (oracleSkip o 1)))) 9 1 (if up = true then 1 else 0)) 10 1
    (if oor = true then 1 else 0)) ex

/-- C1 (`up`) and C2 (`oor`) as condition codes: bits 1 and 2. -/
def ccC1C2 (up oor : Bool) : BitVec 4 := (if oor = true then 4 else 0) ||| ccC1 up

theorem x87SinFsw_eq (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool) (ex : BitVec 6) :
    x87SinFsw fsw o up oor ex =
      fswSetC (fswOrFlags fsw ex) (oBit o 0) (if up = true then 1 else 0)
        (if oor = true then 1 else 0) (oBit o 1) := by
  simp only [x87SinFsw, oBit, oracleSkip_zero]
  fsw_bits
  all_goals cases up <;> cases oor <;> simp [getElem_setSlice]

@[simp] theorem fswTop_x87SinFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool)
    (ex : BitVec 6) : fswTop (x87SinFsw fsw o up oor ex) = fswTop fsw := by
  simp [x87SinFsw_eq]

@[simp] theorem fswES_x87SinFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool)
    (ex : BitVec 6) : fswES (x87SinFsw fsw o up oor ex) = fswES fsw := by
  simp [x87SinFsw_eq]

theorem fswRest_x87SinFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool)
    (ex : BitVec 6) : fswRest (x87SinFsw fsw o up oor ex) = fswOrFlags (fswRest fsw) ex := by
  rw [x87SinFsw_eq]
  fsw_bits

theorem fswCC_x87SinFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool)
    (ex : BitVec 6) : fswCC (x87SinFsw fsw o up oor ex) &&& 6 = ccC1C2 up oor := by
  rw [x87SinFsw_eq, fswCC_fswSetC]
  generalize oBit o 0 = a
  generalize oBit o 1 = b
  revert a b
  cases up <;> cases oor <;> decide

/-- Bit 10 (C2) of `x87SinFsw` is whether the operand was out of range. -/
theorem c2_x87SinFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool) (ex : BitVec 6) :
    (x87SinFsw fsw o up oor ex).extractLsb' 10 1 = if oor = true then 1 else 0 := by
  rw [x87SinFsw_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega : i = 0) with rfl
  cases oor <;> simp [fswSetC, getElem_setSlice]

/-- The status word FCOS leaves: as `x87SinFsw`, but C2 is set before C1, and C1 is the oracle's
next bit when the operand is out of range, as lean-x86 sets them. -/
def x87CosFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool) (ex : BitVec 6) :
    BitVec 16 :=
  fswOrFlags (setSlice (setSlice (setSlice (setSlice (setSlice (setSlice fsw 8 1
    (BitVec.ofBool (oracleBit o))) 9 1 0) 10 1 0) 14 1
    (BitVec.ofBool (oracleBit (oracleSkip o 1)))) 10 1 (if oor = true then 1 else 0)) 9 1
    (if oor = true then BitVec.ofBool (oracleBit (oracleSkip (oracleSkip o 1) 1)) else
      if up = true then 1 else 0)) ex

/-- C1 (`up`, unless `oor`) and C2 (`oor`) of FCOS as condition codes, and the mask of those it
defines: C2, and C1 unless the operand was out of range. -/
def ccCosMask (oor : Bool) : BitVec 4 := if oor = true then 4 else 6

theorem x87CosFsw_eq (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool) (ex : BitVec 6) :
    x87CosFsw fsw o up oor ex =
      fswSetC (fswOrFlags fsw ex) (oBit o 0)
        (if oor = true then oBit o 2 else if up = true then 1 else 0)
        (if oor = true then 1 else 0) (oBit o 1) := by
  simp only [x87CosFsw, oBit, oracleSkip_zero, oracleSkip_oracleSkip]
  fsw_bits
  all_goals cases up <;> cases oor <;> simp [getElem_setSlice]

@[simp] theorem fswTop_x87CosFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool)
    (ex : BitVec 6) : fswTop (x87CosFsw fsw o up oor ex) = fswTop fsw := by
  simp [x87CosFsw_eq]

@[simp] theorem fswES_x87CosFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool)
    (ex : BitVec 6) : fswES (x87CosFsw fsw o up oor ex) = fswES fsw := by
  simp [x87CosFsw_eq]

theorem fswRest_x87CosFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool)
    (ex : BitVec 6) : fswRest (x87CosFsw fsw o up oor ex) = fswOrFlags (fswRest fsw) ex := by
  rw [x87CosFsw_eq]
  fsw_bits

theorem fswCC_x87CosFsw (fsw : BitVec 16) (o : X86.Runtime.Oracle) (up oor : Bool)
    (ex : BitVec 6) :
    fswCC (x87CosFsw fsw o up oor ex) &&& ccCosMask oor = ccC1C2 up oor &&& ccCosMask oor := by
  rw [x87CosFsw_eq, fswCC_fswSetC]
  generalize oBit o 0 = a
  generalize oBit o 1 = b
  generalize oBit o 2 = c
  revert a b c
  cases up <;> cases oor <;> decide

end X86Proofs
