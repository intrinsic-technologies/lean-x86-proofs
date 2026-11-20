import X86Proofs.Core.Float

/-!
# CVTTSS2SI and CVTTSD2SI specification

`CVTTSS2SI r32/r64, xmm1/m32` (`F3 [REX.W] 0F 2C /r`) and `CVTTSD2SI r32/r64, xmm1/m64`
(`F2 [REX.W] 0F 2C /r`) convert the low single- or double-precision element of the source to a
signed doubleword (quadword with REX.W) integer in a general-purpose register, truncating
(rounding toward zero whatever MXCSR.RC says): `DEST ← Convert_To_Integer_Truncate(SRC[e-1:0])`,
with MXCSR's DAZ; a NaN or an out-of-range value gives the integer indefinite value and the
invalid flag, ORed into MXCSR with the other exception flags. The conversion is lean-x86's own
`FP.To_Int` (`fpToInt`, `Core/Float.lean`). `cvtts2siSpec e r mx b` is the `r`-bit result for an
`e`-bit element (the low bits of the source `b`), `cvtts2siFlags e r mx b` the exception flags,
`cvtts2siOk e r mx b` that lean-x86 returns them; lean-x86 computes them with
`Operations.CVTTSf2SI e n r`, which may diverge (`PartialSpecM`).
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The conversion of the low `e` bits of `b` to a signed `r`-bit integer, toward zero. -/
def cvtts2siLane (e r : Nat) {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec r × BitVec 6 :=
  fpToInt e r .Rounding_Mode_RTZ mx (b.extractLsb' 0 e)

/-- The low `e`-bit element of `b` truncated to a signed `r`-bit integer. -/
def cvtts2siSpec (e r : Nat) {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec r :=
  (cvtts2siLane e r mx b).1

/-- The exception flags of the conversion. -/
def cvtts2siFlags (e r : Nat) {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec 6 :=
  (cvtts2siLane e r mx b).2

/-- lean-x86's conversion returns a value (`FpToIntOk`). -/
def cvtts2siOk (e r : Nat) {n : Nat} (mx : BitVec 32) (b : BitVec n) : Prop :=
  FpToIntOk e r .Rounding_Mode_RTZ mx (b.extractLsb' 0 e)

theorem cvtts2si_operation [X86.Machine.Bindings] (e n r : Nat) (he : e = 32 ∨ e = 64)
    (hn : n = e ∨ n = 128) (hr : r = 32 ∨ r = 64) (s : X86.Machine.RamState) (b : BitVec n)
    (hm : MxcsrPre s) (hok : cvtts2siOk e r s.MXCSR b) :
    (X86.Instructions.Operations.CVTTSf2SI e n r b).run s =
      some (.ok (cvtts2siSpec e r s.MXCSR b),
        { s with MXCSR := mxOr s.MXCSR (cvtts2siFlags e r s.MXCSR b) }) := by
  rcases he with rfl | rfl <;> rcases hn with rfl | rfl <;> rcases hr with rfl | rfl <;>
    unfold X86.Instructions.Operations.CVTTSf2SI <;>
    simp (config := { decide := true }) only [x86_runtime, pure_bind] <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_ <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_ <;>
    refine (partialSpecM_bind_run _ _ (partialResult_lift_run (fpToInt_run _ _ _ _ _ hok) _)).trans
      ?_ <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (checkExceptions_run _ _ hm)).trans ?_ <;>
    rfl

end X86Proofs
