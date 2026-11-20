import X86Proofs.Core.Float

/-!
# RCPSS specification

`RCPSS xmm1, xmm2/m32` (`F3 0F 53 /r`) computes an approximation of the reciprocal of the low
single-precision element of the source: `DEST[31:0] ← APPROXIMATE(1.0 / SRC[31:0])`,
`DEST[127:32]` unchanged. It reads and writes no MXCSR state and raises no SIMD floating-point
exception. The approximation is lean-x86's `FP.Reciprocal` (`fpRcp`, `Core/Float.lean`): special
values (NaN, infinity, zero, denormal) by lean-x86's own rules, a normal value by the machine's
numerical binding `Emulate_RCPSS`. `rcpssSpec a b` is the result, `rcpssOk a b` that lean-x86
returns a value on `b`, the same from every state (`FpRcpOk`); lean-x86 computes it with
`Operations.RCPSf 32 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The approximate reciprocal of `b` in the low element of `a`, the rest of `a` kept. -/
def rcpssSpec [X86.Machine.Bindings] (a : BitVec 128) (b : BitVec 32) : BitVec 128 :=
  fpScalar 32 a (fpRcp b)

/-- lean-x86's approximation returns a value on `b` (`FpRcpOk`). -/
def rcpssOk [X86.Machine.Bindings] (_a : BitVec 128) (b : BitVec 32) : Prop := FpRcpOk b

theorem rcpss_operation [X86.Machine.Bindings] (s : X86.Machine.RamState) (a : BitVec 128)
    (b : BitVec 32) (hok : rcpssOk a b) :
    (X86.Instructions.Operations.RCPSf 32 128 a b).run s = (.ok (rcpssSpec a b), s) := by
  unfold X86.Instructions.Operations.RCPSf
  simp (config := { decide := true }) only [x86_runtime, pure_bind]
  refine (specM_bind_run _ _ (fpRcp_run _ _ hok)).trans ?_
  simp only [x86_runtime, BitVec.cast_eq]
  rw [setSlice_scalar _ (by decide)]
  rfl

end X86Proofs
