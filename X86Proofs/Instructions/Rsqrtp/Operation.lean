import X86Proofs.Core.Float

/-!
# RSQRTPS specification

`RSQRTPS xmm1, xmm2/m128` (`NP 0F 52 /r`) computes an approximation of the reciprocal square root
of each single-precision element of the source:
`DEST[32i+31:32i] ← APPROXIMATE(1.0 / SQRT(SRC[32i+31:32i]))` for `i` = 0 to 3. It reads and
writes no MXCSR state and raises no SIMD floating-point exception. Each lane is lean-x86's
`FP.Reciprocal_Sqrt` (`fpRsqrt`, `Core/Float.lean`): special values by lean-x86's own rules, a
normal positive value by the machine's numerical binding `Emulate_RSQRTSS`. `rsqrtpsSpec a b` is
the result (the destination `a` is not read), `rsqrtpsOk a b` that lean-x86 returns a value on
every lane, the same from every state (`FpRsqrtOk`); lean-x86 computes it with
`Operations.RSQRTPf 32 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The approximate reciprocal square roots of the single-precision lanes of `b`. -/
def rsqrtpsSpec [X86.Machine.Bindings] (_a b : BitVec 128) : BitVec 128 :=
  ofLanes 128 32 fun i => fpRsqrt (lane 32 b i)

/-- lean-x86's approximation returns a value on every lane (`FpRsqrtOk`). -/
def rsqrtpsOk [X86.Machine.Bindings] (_a b : BitVec 128) : Prop :=
  ∀ i < 4, FpRsqrtOk (lane 32 b i)

theorem rsqrtps_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a b : BitVec 128)
    (hok : rsqrtpsOk a b) :
    (X86.Instructions.Operations.RSQRTPf 32 128 b).run s = (.ok (rsqrtpsSpec a b), s) := by
  unfold X86.Instructions.Operations.RSQRTPf
  simp (config := { decide := true }) only [x86_runtime, Int.reduceBEq, Bool.true_or, pure_bind]
  refine (specM_bind_run _ _ (specM_forIn_lanes _ _ _
    (fun i r => X86.Runtime.setSlice r (i * 32) 32 (fpRsqrt (lane 32 b i))) _ ?_)).trans ?_
  · intro i hi r
    have hik : i < 4 := by simpa using hi
    have h0 : (0 : Int) ≤ (i : Int) * 32 := by omega
    have h1 : (i : Int) * 32 + 32 ≤ 128 := by omega
    have h2 : (i : Int) * 32 ≤ 96 := by omega
    simp only [Int.zero_add, h2, decide_true, assert_of_true, pure_bind,
      sliceElement_bitVec_eq_pure _ h0 (by decide) h1, natCast_mul_toNat i 32 (by decide),
      Int.reduceToNat, extractLsb'_eq_lane]
    refine (specM_bind_run _ _ (fpRsqrt_run _ _ (hok i hik))).trans ?_
    rw [setSliceChecked_eq_pure _ _ h0 (by decide) h1]
    simp only [pure_bind, natCast_mul_toNat i 32 (by decide), Int.reduceToNat]
    rfl
  · rfl

end X86Proofs
