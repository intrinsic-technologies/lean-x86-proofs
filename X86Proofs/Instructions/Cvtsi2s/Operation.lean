import X86Proofs.Core.Float

/-!
# CVTSI2SS and CVTSI2SD specification

`CVTSI2SS xmm1, r/m32` / `CVTSI2SS xmm1, r/m64` (`F3 [REX.W] 0F 2A /r`) and `CVTSI2SD xmm1,
r/m32` / `CVTSI2SD xmm1, r/m64` (`F2 [REX.W] 0F 2A /r`) convert a signed doubleword (quadword with
REX.W) integer to single or double precision in the low element of the destination:
`DEST[r-1:0] ← Convert(SRC)`, `DEST[127:r]` unchanged, rounded as MXCSR.RC says; the exception
flags (precision only) are ORed into MXCSR. The conversion is lean-x86's own `FP.From_Int`
(`fpFromInt`, `Core/Float.lean`); there is no IEEE-754 library to state it against
independently. `cvtsi2sSpec e r mx a b` is the result for an `e`-bit integer `b` and an `r`-bit
float, `cvtsi2sFlags e r mx a b` the exception flags, `cvtsi2sOk e r mx a b` that lean-x86 returns
them; lean-x86 computes them with `Operations.CVTSI2Sf e 128 r e`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The `e`-bit signed integer `b` in the low `r` bits of `a`, the rest of `a` kept. -/
def cvtsi2sSpec (e r : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : BitVec 128 :=
  fpScalar r a (fpFromInt e r mx b).1

/-- The exception flags of the conversion. -/
def cvtsi2sFlags (e r : Nat) (mx : BitVec 32) (_a : BitVec 128) (b : BitVec e) : BitVec 6 :=
  (fpFromInt e r mx b).2

/-- lean-x86's conversion returns a value on `b` (`FpFromIntOk`). -/
def cvtsi2sOk (e r : Nat) (mx : BitVec 32) (_a : BitVec 128) (b : BitVec e) : Prop :=
  FpFromIntOk e r mx b

theorem cvtsi2s_operation [X86.Machine.Bindings] (e r : Nat) (he : e = 32 ∨ e = 64)
    (hr : r = 32 ∨ r = 64) (s : X86.Machine.RamState) (a : BitVec 128) (b : BitVec e)
    (ctx : Instruction_Context) (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s)
    (hok : cvtsi2sOk e r s.MXCSR a b) :
    (X86.Instructions.Operations.CVTSI2Sf e 128 r e a b ctx mod).run s =
      (.ok (cvtsi2sSpec e r s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (cvtsi2sFlags e r s.MXCSR a b) }) := by
  rcases he with rfl | rfl <;> rcases hr with rfl | rfl <;>
    unfold X86.Instructions.Operations.CVTSI2Sf <;>
    simp (config := { decide := true }) only [x86_runtime, hb, Int.reduceBEq, Bool.true_or,
      Bool.or_true, pure_bind, BitVec.reduceBEq] <;>
    refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_ <;>
    simp only [and_false_left, Bool.false_eq_true, ↓reduceIte] <;>
    refine (specM_bind_run _ _ (mxcsrRC_run _)).trans ?_ <;>
    refine (specM_bind_run _ _ (liftM_run_of_ok (decodeRoundingMode_eq _) _)).trans ?_ <;>
    rw [extractLsb'_zero_self] <;>
    refine (specM_bind_run _ _ (fpFromInt_run _ _ (by decide) (by decide) _ _ hok)).trans ?_ <;>
    refine (specM_bind_run _ _ (checkExceptions_run _ _ hm)).trans ?_ <;>
    simp only [x86_runtime, BitVec.cast_eq] <;>
    rw [setSlice_scalar _ (by decide)] <;>
    rfl

end X86Proofs
