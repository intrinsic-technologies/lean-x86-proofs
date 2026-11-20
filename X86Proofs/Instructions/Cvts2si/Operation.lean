import X86Proofs.Core.Float

/-!
# CVTSS2SI and CVTSD2SI specification

`CVTSS2SI r32/r64, xmm1/m32` (`F3 [REX.W] 0F 2D /r`) and `CVTSD2SI r32/r64, xmm1/m64`
(`F2 [REX.W] 0F 2D /r`) convert the low single- or double-precision element of the source to a
signed doubleword (quadword with REX.W) integer in a general-purpose register:
`DEST ← Convert_To_Integer(SRC[e-1:0])`, rounded as MXCSR.RC says, with MXCSR's DAZ; a NaN or an
out-of-range value gives the integer indefinite value (`80000000H`, `8000000000000000H`) and the
invalid flag, ORed into MXCSR with the other exception flags. The conversion is lean-x86's own
`FP.To_Int` (`fpToInt`, `Core/Float.lean`); there is no IEEE-754 library to state it against
independently. `cvts2siSpec e r mx b` is the `r`-bit result for an `e`-bit element (the low bits
of the source `b`: an XMM register or the memory operand), `cvts2siFlags e r mx b` the exception
flags, `cvts2siOk e r mx b` that lean-x86 returns them; lean-x86 computes them with
`Operations.CVTSf2SI e n r`, which may diverge (`PartialSpecM`).
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The conversion of the low `e` bits of `b` to a signed `r`-bit integer at MXCSR `mx`. -/
def cvts2siLane (e r : Nat) {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec r × BitVec 6 :=
  fpToInt e r (rcMode (mxRc mx)) mx (b.extractLsb' 0 e)

/-- The low `e`-bit element of `b` converted to a signed `r`-bit integer. -/
def cvts2siSpec (e r : Nat) {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec r :=
  (cvts2siLane e r mx b).1

/-- The exception flags of the conversion. -/
def cvts2siFlags (e r : Nat) {n : Nat} (mx : BitVec 32) (b : BitVec n) : BitVec 6 :=
  (cvts2siLane e r mx b).2

/-- lean-x86's conversion returns a value (`FpToIntOk`). -/
def cvts2siOk (e r : Nat) {n : Nat} (mx : BitVec 32) (b : BitVec n) : Prop :=
  FpToIntOk e r (rcMode (mxRc mx)) mx (b.extractLsb' 0 e)

theorem cvts2si_operation [X86.Machine.Bindings] (e n r : Nat) (he : e = 32 ∨ e = 64)
    (hn : n = e ∨ n = 128) (hr : r = 32 ∨ r = 64) (s : X86.Machine.RamState) (b : BitVec n)
    (ctx : Instruction_Context) (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s)
    (hok : cvts2siOk e r s.MXCSR b) :
    (X86.Instructions.Operations.CVTSf2SI e n r b ctx mod).run s =
      some (.ok (cvts2siSpec e r s.MXCSR b),
        { s with MXCSR := mxOr s.MXCSR (cvts2siFlags e r s.MXCSR b) }) := by
  rcases he with rfl | rfl <;> rcases hn with rfl | rfl <;> rcases hr with rfl | rfl <;>
    unfold X86.Instructions.Operations.CVTSf2SI <;>
    simp (config := { decide := true }) only [x86_runtime, hb, pure_bind, BitVec.reduceBEq] <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_ <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrMasks_run _)).trans ?_ <;>
    simp only [and_false_left, Bool.false_eq_true, ↓reduceIte] <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (mxcsrRC_run _)).trans ?_ <;>
    refine (partialSpecM_bind_run _ _
      (partialSpecM_liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_ <;>
    refine (partialSpecM_bind_run _ _ (partialResult_lift_run (fpToInt_run _ _ _ _ _ hok) _)).trans
      ?_ <;>
    refine (partialSpecM_liftTotal_bind_run _ _ (checkExceptions_run _ _ hm)).trans ?_ <;>
    rfl

end X86Proofs
