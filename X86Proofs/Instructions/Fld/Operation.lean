import X86Proofs.Core.X87Mem

/-!
# FLD specification

`FLD ST(i)`: push ST(i) onto the register stack (TOP := TOP − 1, then ST(0) := the old ST(i)); the
constant loads (FLD1, FLDZ, FLDPI, …), `FLD m80fp` and FILD push a value the same way. lean-x86's
`Operations.FLD` leaves C1 := 0 and draws C0, C2, C3 from its oracle; with the source not empty (a
register source) and the push slot (ST(7) before the push) empty there is no stack fault and no
exception, and the value is loaded unchanged.

`FLD m32fp`, `FLD m64fp` (`Operations.FLD_Convert`) push the converted operand (`x87FromFloat`)
the same way, except that a signalling NaN is pushed as its quiet NaN with the invalid-operation
flag IE, and a denormal operand raises the denormal flag DE (`fldConvertSpec`).
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The status word `Operations.FLD` leaves: C0, C2, C3 from the oracle `o`, C1 := 0, no
exception flag. -/
def fldStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) : BitVec 16 :=
  fswOrFlags (fswSetC fsw (oBit o 0) 0 (oBit o 1) (oBit o 2)) 0

@[simp] theorem fswTop_fldStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswTop (fldStatus fsw o) = fswTop fsw := by
  simp [fldStatus]

@[simp] theorem fswES_fldStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswES (fldStatus fsw o) = fswES fsw := by
  simp [fldStatus]

theorem fswRest_fldStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswRest (fldStatus fsw o) = fswRest fsw := by
  simp [fldStatus]

theorem fswCC_fldStatus_c1 (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswCC (fldStatus fsw o) &&& 2 = 0 := by
  simp only [fldStatus, fswCC_fswOrFlags, fswCC_fswSetC]
  generalize oBit o 0 = a
  generalize oBit o 1 = b
  generalize oBit o 2 = c
  revert a b c
  decide

/-- `FLD m32fp` / `FLD m64fp` of the converted operand `x` (`d`: the memory operand was a
denormal): the value pushed and the exception flags (bit 0 IE, bit 1 DE). -/
def fldConvertSpec (x : BitVec 80) (d : Bool) : BitVec 80 × BitVec 6 :=
  if fp87Class x = .FP87_Class_SNaN then (x87Quiet x, 1) else (x, if d then 2 else 0)

/-- The status word `Operations.FLD_Convert` leaves: C0, C2, C3 from the oracle `o`, C1 := 0, the
exception flags `ex` ORed in. -/
def fldConvStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (ex : BitVec 6) : BitVec 16 :=
  fswOrFlags (fswSetC fsw (oBit o 0) 0 (oBit o 1) (oBit o 2)) ex

@[simp] theorem fswTop_fldConvStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (ex : BitVec 6) :
    fswTop (fldConvStatus fsw o ex) = fswTop fsw := by
  simp [fldConvStatus]

@[simp] theorem fswES_fldConvStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (ex : BitVec 6) :
    fswES (fldConvStatus fsw o ex) = fswES fsw := by
  simp [fldConvStatus]

theorem fswRest_fldConvStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) (ex : BitVec 6) :
    fswRest (fldConvStatus fsw o ex) = fswOrFlags (fswRest fsw) ex := by
  unfold fldConvStatus
  fsw_bits

theorem fswCC_fldConvStatus_c1 (fsw : BitVec 16) (o : X86.Runtime.Oracle) (ex : BitVec 6) :
    fswCC (fldConvStatus fsw o ex) &&& 2 = 0 := by
  simp only [fldConvStatus, fswCC_fswOrFlags, fswCC_fswSetC]
  generalize oBit o 0 = a
  generalize oBit o 1 = b
  generalize oBit o 2 = c
  revert a b c
  decide

theorem fld_operation {σ : Type} (s : X86.State σ) (src : BitVec 80) (i : BitVec 3)
    (isMem : Bool) (hsrc : isMem = true ∨ ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) ≠ 3)
    (hpush : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) = 3)
    (hm : FcwMasked s.FP87_Control) :
    (X86.Instructions.Operations.FLD src i isMem : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (src, true), { s with
        oracle := oracleSkip s.oracle 3
        FP87_Status := fldStatus s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FLD
  spec_run [FP87.Is_STi_Empty =>
      isSTiEmpty_run _ _ (by first | decide | exact unsigned_range _ rfl),
    X86.UNSPECIFIED => unspecified1_run _]
  have hsrc' : (!isMem && (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) == 3)) = false := by
    rcases hsrc with h | h
    · simp [h]
    · cases isMem <;> simp <;> exact h
  have hpush' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) == 3) = true := by
    simpa using hpush
  x87_cond [hsrc', hpush']
  spec_run [X86.FP87_Control.IM => fp87ControlIM_run _,
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]

theorem fld_convert_operation {σ : Type} (s : X86.State σ) (x : BitVec 80) (d : Bool)
    (hpush : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) = 3)
    (hm : FcwMasked s.FP87_Control) :
    (X86.Instructions.Operations.FLD_Convert x d : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok ((fldConvertSpec x d).1, true), { s with
        oracle := oracleSkip s.oracle 3
        FP87_Status := fldConvStatus s.FP87_Status s.oracle (fldConvertSpec x d).2 }) := by
  unfold X86.Instructions.Operations.FLD_Convert
  spec_run [FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide),
    X86.UNSPECIFIED => unspecified1_run _]
  have hpush' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + 7) == 3) = true := by
    simpa using hpush
  x87_cond [hpush']
  have him := fcwMasked_im hm
  refine (specM_bind_run _ _ (liftM_run_of_ok (classify_eq x) _)).trans ?_
  by_cases hc : fp87Class x = .FP87_Class_SNaN
  · simp only [hc, beq_self_eq_true, ↓reduceIte, fldConvertSpec]
    spec_run [liftM => liftM_run_of_ok (quietizeNaN_eq x hc) _,
      X86.FP87_Control.IM => fp87ControlIM_run _,
      FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]
    simp only [him]
    rfl
  · have hc' : (fp87Class x == .FP87_Class_SNaN) = false := by simpa using hc
    simp only [fldConvertSpec, hc, hc', Bool.false_eq_true, ite_false]
    cases d <;> spec_run [X86.FP87_Control.IM => fp87ControlIM_run _,
        FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]

end X86Proofs
