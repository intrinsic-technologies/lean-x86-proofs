import X86Proofs.Core.X87

/-!
# FXAM specification

`FXAM`: classify ST(0) into C3, C2, C0 (`fxamCode`: unsupported 000, NaN 001, normal 010, infinity
011, zero 100, empty 101, denormal 110) and C1 := its sign bit. An empty ST(0) is classified, not a
fault, so FXAM needs no tag condition. All four condition codes are defined; no oracle bit is
used.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The class FXAM reports as `C3 C2 C0` (as one 3-bit value, bit 0 = C0, bit 1 = C2, bit 2 = C3)
for a register tagged empty or not and of class `c` (`fp87Class`). -/
def fxamCode (empty : Bool) (c : FP87_Class_Type) : BitVec 3 :=
  if empty then 5 else
    match c with
    | .FP87_Class_Unsupported => 0
    | .FP87_Class_QNaN | .FP87_Class_SNaN => 1
    | .FP87_Class_Normal => 2
    | .FP87_Class_Infinity => 3
    | .FP87_Class_Zero => 4
    | .FP87_Class_Denormal => 6

/-- The status word FXAM leaves: C0, C2, C3 from `fxamCode` of ST(0), C1 := its sign. -/
def fxamStatus (fsw : BitVec 16) (empty : Bool) (v : BitVec 80) : BitVec 16 :=
  let c := fxamCode empty (fp87Class v)
  fswSetC fsw (c.extractLsb' 0 1) (fprSign v) (c.extractLsb' 1 1) (c.extractLsb' 2 1)

/-- The condition codes FXAM leaves (`C3 C2 C1 C0`, as `fswCC` orders them). -/
def fxamCC (empty : Bool) (v : BitVec 80) : BitVec 4 :=
  let c := fxamCode empty (fp87Class v)
  c.extractLsb' 2 1 ++ c.extractLsb' 1 1 ++ fprSign v ++ c.extractLsb' 0 1

@[simp] theorem fswTop_fxamStatus (fsw : BitVec 16) (empty : Bool) (v : BitVec 80) :
    fswTop (fxamStatus fsw empty v) = fswTop fsw := by
  simp [fxamStatus]

@[simp] theorem fswES_fxamStatus (fsw : BitVec 16) (empty : Bool) (v : BitVec 80) :
    fswES (fxamStatus fsw empty v) = fswES fsw := by
  simp [fxamStatus]

theorem fswRest_fxamStatus (fsw : BitVec 16) (empty : Bool) (v : BitVec 80) :
    fswRest (fxamStatus fsw empty v) = fswRest fsw := by
  simp [fxamStatus]

theorem fswCC_fxamStatus (fsw : BitVec 16) (empty : Bool) (v : BitVec 80) :
    fswCC (fxamStatus fsw empty v) = fxamCC empty v := by
  simp [fxamStatus, fxamCC]

theorem fxam_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.FXAM : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        FP87_Status := fxamStatus s.FP87_Status
          (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3)
          s.FP87[fprIndex (fswTop s.FP87_Status)] }) := by
  unfold X86.Instructions.Operations.FXAM
  simp only [bind_assoc, unsigned_eq, assert_toNatW_lt8, assert_natCast_nonneg, pure_bind,
    Int.reduceToNat]
  spec_run_until [X86.FP87_Status.TOP => fp87StatusTOP_run _,
    X86.FP87.get => fp87Get_run _ _ _ rfl, FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  simp only [show BitVec.ofInt 3 0 = 0 from rfl, add_zero3', fxamStatus]
  by_cases he : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) = 3
  · simp only [he, beq_self_eq_true, ↓reduceIte, fxamCode]
    spec_run []
  · have he' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using he
    simp only [he', Bool.false_eq_true, ↓reduceIte, fxamCode]
    spec_run_until [liftM => liftM_run_of_ok (classify_eq _) _]
    cases fp87Class s.FP87[fprIndex (fswTop s.FP87_Status)] <;> spec_run []

end X86Proofs
