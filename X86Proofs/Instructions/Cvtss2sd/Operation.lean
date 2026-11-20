import X86Proofs.Core.Float

/-!
# CVTSS2SD specification

`CVTSS2SD xmm1, xmm2/m32` (`F3 0F 5A /r`) converts the low single-precision element of the source
to double precision: `DEST[63:0] ← Convert(SRC[31:0])`, `DEST[127:64]` unchanged, with MXCSR's
DAZ (the conversion is exact, so no rounding, and lean-x86 flushes a tiny result to zero), and the
exception flags ORed into MXCSR. The conversion and its flags are lean-x86's own `FP.Convert` at
that MXCSR (`fpConvert`, `Core/Float.lean`); there is no IEEE-754 library to state them against
independently. `cvtss2sdSpec mx a b` is the result, `cvtss2sdFlags mx a b` the exception flags,
`cvtss2sdOk mx a b` that lean-x86 returns them; lean-x86 computes both with
`Operations.CVTSf2Sg 32 128 64 32`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The conversion of `b` at MXCSR `mx` (round to nearest even, flush to zero). -/
def cvtss2sdLane (mx : BitVec 32) (b : BitVec 32) : BitVec 64 × BitVec 6 :=
  fpConvert 32 64 .Rounding_Mode_RNE true mx b

/-- `b` converted to double precision in the low element of `a`, the rest of `a` kept. -/
def cvtss2sdSpec (mx : BitVec 32) (a : BitVec 128) (b : BitVec 32) : BitVec 128 :=
  fpScalar 64 a (cvtss2sdLane mx b).1

/-- The exception flags of the conversion. -/
def cvtss2sdFlags (mx : BitVec 32) (_a : BitVec 128) (b : BitVec 32) : BitVec 6 :=
  (cvtss2sdLane mx b).2

/-- lean-x86's conversion returns a value on `b` (`FpConvertOk`). -/
def cvtss2sdOk (mx : BitVec 32) (_a : BitVec 128) (b : BitVec 32) : Prop :=
  FpConvertOk 32 64 .Rounding_Mode_RNE true mx b

theorem cvtss2sd_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a : BitVec 128)
    (b : BitVec 32) (hm : MxcsrPre s) (hok : cvtss2sdOk s.MXCSR a b) :
    (X86.Instructions.Operations.CVTSf2Sg 32 128 64 32 a b).run s =
      (.ok (cvtss2sdSpec s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtss2sdFlags s.MXCSR a b) }) := by
  unfold X86.Instructions.Operations.CVTSf2Sg
  simp (config := { decide := true }) only [x86_runtime, Int.reduceBEq, Bool.true_or, pure_bind]
  refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
  rw [extractLsb'_zero_self]
  refine (specM_bind_run _ _ (fpConvert_run 32 64 (.inl ⟨rfl, rfl⟩) _ _ _ _ hok)).trans ?_
  refine (specM_bind_run _ _ (checkExceptions_run _ _ hm)).trans ?_
  simp only [x86_runtime, BitVec.cast_eq]
  rw [setSlice_scalar _ (by decide)]
  rfl

end X86Proofs
