import X86Proofs.Instructions.Fld.Operation
import X86Proofs.Program.ReadWrite.X87

/-!
# FLD1, FLDL2T, FLDL2E, FLDPI, FLDLG2, FLDLN2, FLDZ specification

Push a constant (`D9 E8`…`EE`): +1.0, log₂10, log₂e, π, log₁₀2, ln 2, +0.0 (lean-x86's
`FP87.One`, `FP87.Log2_Ten`, `FP87.Log2_e`, `FP87.Pi`, `FP87.Log10_Two`, `FP87.Natural_Log_Two`,
`FP87.Zero`; `x87Const` with index 0 to 6). The irrational constants are rounded to the 64-bit
significand by the rounding control RC (FCW bits 10–11): `x87ConstBase` is the value rounded down,
one more in the last place when it rounds up (`x87ConstRoundsUp`: log₂10 rounds up only toward +∞,
RC = 2; log₂e, π, log₁₀2 and ln 2 also to nearest, RC = 0). The load itself is
`Operations.FLD_Constant` (C1 := 0, C0, C2, C3 from the oracle; `fldStatus`, as `Operations.FLD`).
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The constants rounded down, as 80-bit values: +1.0, log₂10, log₂e, π, log₁₀2, ln 2, +0.0. -/
def x87ConstBase : Nat → BitVec 80
  | 0 => 0x3FFF8000000000000000
  | 1 => 0x4000D49A784BCD1B8AFE
  | 2 => 0x3FFFB8AA3B295C17F0BB
  | 3 => 0x4000C90FDAA22168C234
  | 4 => 0x3FFD9A209A84FBCFF798
  | 5 => 0x3FFEB17217F7D1CF79AB
  | _ => 0

/-- Whether constant `idx` rounds up (one more in the last place) under rounding control `rc`. -/
def x87ConstRoundsUp (idx : Nat) (rc : BitVec 2) : Bool :=
  match idx with
  | 1 => rc == 2
  | 2 | 3 | 4 | 5 => rc == 2 || rc == 0
  | _ => false

/-- Constant `idx` under rounding control `rc`.

| Index | Instruction | lean-x86 helper |
| --- | --- | --- |
| 0 | FLD1 | `FP87.One` |
| 1 | FLDL2T | `FP87.Log2_Ten` |
| 2 | FLDL2E | `FP87.Log2_e` |
| 3 | FLDPI | `FP87.Pi` |
| 4 | FLDLG2 | `FP87.Log10_Two` |
| 5 | FLDLN2 | `FP87.Natural_Log_Two` |
| 6 | FLDZ | `FP87.Zero` |
-/
def x87Const (idx : Nat) (rc : BitVec 2) : BitVec 80 :=
  if x87ConstRoundsUp idx rc then x87ConstBase idx + 1 else x87ConstBase idx

theorem bv2_cases (r : BitVec 2) : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by
  revert r; decide

theorem fp87One_eq (rc : BitVec 2) : FP87.One 0 = .ok (x87Const 0 rc) := rfl

theorem fp87Zero_eq (rc : BitVec 2) : FP87.Zero 0 = .ok (x87Const 6 rc) := rfl

theorem fp87Log2Ten_run {σ : Type} (s : X86.State σ) :
    (FP87.Log2_Ten : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (x87Const 1 (fcwRC s.FP87_Control)), s) := by
  unfold FP87.Log2_Ten FP87.Get_Rounding_Mode
  spec_run_until [X86.FP87_Control.RC => fp87ControlRC_run _]
  simp only [Int.reduceToNat, fcwRC]
  rcases bv2_cases (s.FP87_Control.extractLsb' 10 2) with h | h | h | h <;> simp only [h] <;> rfl

theorem fp87Log2e_run {σ : Type} (s : X86.State σ) :
    (FP87.Log2_e : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (x87Const 2 (fcwRC s.FP87_Control)), s) := by
  unfold FP87.Log2_e FP87.Get_Rounding_Mode
  spec_run_until [X86.FP87_Control.RC => fp87ControlRC_run _]
  simp only [Int.reduceToNat, fcwRC]
  rcases bv2_cases (s.FP87_Control.extractLsb' 10 2) with h | h | h | h <;> simp only [h] <;> rfl

theorem fp87Pi_run {σ : Type} (s : X86.State σ) :
    (FP87.Pi : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (x87Const 3 (fcwRC s.FP87_Control)), s) := by
  unfold FP87.Pi FP87.Get_Rounding_Mode
  spec_run_until [X86.FP87_Control.RC => fp87ControlRC_run _]
  simp only [Int.reduceToNat, fcwRC]
  rcases bv2_cases (s.FP87_Control.extractLsb' 10 2) with h | h | h | h <;> simp only [h] <;> rfl

theorem fp87Log10Two_run {σ : Type} (s : X86.State σ) :
    (FP87.Log10_Two : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (x87Const 4 (fcwRC s.FP87_Control)), s) := by
  unfold FP87.Log10_Two FP87.Get_Rounding_Mode
  spec_run_until [X86.FP87_Control.RC => fp87ControlRC_run _]
  simp only [Int.reduceToNat, fcwRC]
  rcases bv2_cases (s.FP87_Control.extractLsb' 10 2) with h | h | h | h <;> simp only [h] <;> rfl

theorem fp87NaturalLogTwo_run {σ : Type} (s : X86.State σ) :
    (FP87.Natural_Log_Two : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (x87Const 5 (fcwRC s.FP87_Control)), s) := by
  unfold FP87.Natural_Log_Two FP87.Get_Rounding_Mode
  spec_run_until [X86.FP87_Control.RC => fp87ControlRC_run _]
  simp only [Int.reduceToNat, fcwRC]
  rcases bv2_cases (s.FP87_Control.extractLsb' 10 2) with h | h | h | h <;> simp only [h] <;> rfl

theorem fldConstant_operation {σ : Type} (s : X86.State σ) (v : BitVec 80)
    (hpush : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) = 3)
    (hm : FcwMasked s.FP87_Control) :
    (X86.Instructions.Operations.FLD_Constant v : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (v, true), { s with
        oracle := oracleSkip s.oracle 3
        FP87_Status := fldStatus s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FLD_Constant
  spec_run [FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide),
    X86.UNSPECIFIED => unspecified1_run _]
  have hpush' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) == 3) = true := by
    simpa using hpush
  x87_cond [hpush']
  spec_run [FP87.Is_Unmasked_Pre_Computation_Exception => isUnmaskedPre_masked _ _ (by exact hm),
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]

end X86Proofs
