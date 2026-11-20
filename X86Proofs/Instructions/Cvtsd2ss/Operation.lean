import X86Proofs.Core.Float

/-!
# CVTSD2SS specification

`CVTSD2SS xmm1, xmm2/m64` (`F2 0F 5A /r`) converts the low double-precision element of the source
to single precision: `DEST[31:0] ← Convert(SRC[63:0])`, `DEST[127:32]` unchanged, rounded as
MXCSR.RC says, with MXCSR's DAZ and FTZ, and the exception flags ORed into MXCSR. The conversion and
its flags are lean-x86's own `FP.Convert` at that MXCSR (`fpConvert`, `Core/Float.lean`); there is
no IEEE-754 library to state them against independently. `cvtsd2ssSpec mx a b` is the result,
`cvtsd2ssFlags mx a b` the exception flags, `cvtsd2ssOk mx a b` that lean-x86 returns them;
lean-x86 computes both with `Operations.CVTSg2Sf 64 128 32 64`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The conversion of `b` at MXCSR `mx` (MXCSR's rounding control and FTZ). -/
def cvtsd2ssLane (mx : BitVec 32) (b : BitVec 64) : BitVec 32 × BitVec 6 :=
  fpConvert 64 32 (rcMode (mxRc mx)) (mxFtz mx) mx b

/-- `b` converted to single precision in the low element of `a`, the rest of `a` kept. -/
def cvtsd2ssSpec (mx : BitVec 32) (a : BitVec 128) (b : BitVec 64) : BitVec 128 :=
  fpScalar 32 a (cvtsd2ssLane mx b).1

/-- The exception flags of the conversion. -/
def cvtsd2ssFlags (mx : BitVec 32) (_a : BitVec 128) (b : BitVec 64) : BitVec 6 :=
  (cvtsd2ssLane mx b).2

/-- lean-x86's conversion returns a value on `b` (`FpConvertOk`). -/
def cvtsd2ssOk (mx : BitVec 32) (_a : BitVec 128) (b : BitVec 64) : Prop :=
  FpConvertOk 64 32 (rcMode (mxRc mx)) (mxFtz mx) mx b

theorem cvtsd2ss_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a : BitVec 128)
    (b : BitVec 64) (ctx : Instruction_Context) (mod : BitVec 2) (hb : ctx.evex_b = 0)
    (hm : MxcsrPre s) (hok : cvtsd2ssOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTSg2Sf 64 128 32 64 a b ctx mod).run s =
      (.ok (cvtsd2ssSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtsd2ssFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTSg2Sf
  simp (config := { decide := true }) only [x86_runtime, hb, Int.reduceBEq, Bool.true_or,
    pure_bind, BitVec.reduceBEq]
  refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (getFTZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_
  refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_
  rw [extractLsb'_zero_self]
  refine (specM_bind_run _ _ (fpConvert_run 64 32 (.inr ⟨rfl, rfl⟩) _ _ _ _ hok)).trans ?_
  refine (specM_bind_run _ _ (checkExceptions_run _ _ hm)).trans ?_
  simp only [x86_runtime, BitVec.cast_eq]
  rw [setSlice_scalar _ (by decide)]
  rfl

end X86Proofs
