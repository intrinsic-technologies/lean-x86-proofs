import X86Proofs.Core.Float

/-!
# RSQRTSS specification

`RSQRTSS xmm1, xmm2/m32` (`F3 0F 52 /r`) computes an approximation of the reciprocal square root
of the low single-precision element of the source:
`DEST[31:0] ← APPROXIMATE(1.0 / SQRT(SRC[31:0]))`, `DEST[127:32]` unchanged. It reads and writes no
MXCSR state and raises no SIMD floating-point exception. The approximation is lean-x86's
`FP.Reciprocal_Sqrt` (`fpRsqrt`, `Core/Float.lean`): special values (NaN, infinity, zero, a
negative value, denormal) by lean-x86's own rules, a normal positive value by the machine's
numerical binding `Emulate_RSQRTSS`. `rsqrtssSpec a b` is the result, `rsqrtssOk a b` that
lean-x86 returns a value on `b`, the same from every state (`FpRsqrtOk`); lean-x86 computes it
with `Operations.RSQRTSf 32 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The approximate reciprocal square root of `b` in the low element of `a`, the rest of `a`
kept. -/
def rsqrtssSpec [X86.Machine.Bindings] (a : BitVec 128) (b : BitVec 32) : BitVec 128 :=
  fpScalar 32 a (fpRsqrt b)

/-- lean-x86's approximation returns a value on `b` (`FpRsqrtOk`). -/
def rsqrtssOk [X86.Machine.Bindings] (_a : BitVec 128) (b : BitVec 32) : Prop := FpRsqrtOk b

theorem rsqrtss_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a : BitVec 128)
    (b : BitVec 32) (hok : rsqrtssOk a b) :
    (X86.Instructions.Operations.RSQRTSf 32 128 a b).run s = (.ok (rsqrtssSpec a b), s) := by
  unfold X86.Instructions.Operations.RSQRTSf
  simp (config := { decide := true }) only [x86_runtime, pure_bind]
  refine (specM_bind_run _ _ (fpRsqrt_run _ _ hok)).trans ?_
  simp only [x86_runtime, BitVec.cast_eq]
  rw [setSlice_scalar _ (by decide)]
  rfl

end X86Proofs
