import X86Proofs.Core.Float

/-!
# SQRTSS, SQRTSD specification

`SQRTSS xmm1, xmm2/m32` (`F3 0F 51 /r`) and `SQRTSD xmm1, xmm2/m64` (`F2 0F 51 /r`) take the
square root of the low single- or double-precision element of the source: `DEST[e-1:0] ←
SQRT(SRC[e-1:0])`, `DEST[127:e]` unchanged (`e` = 32 or 64), rounded as MXCSR.RC says, with
MXCSR's DAZ and FTZ, and the exception flags ORed into MXCSR. The root and its flags are
lean-x86's own `FP.Sqrt` at that MXCSR (`fpSqrt`, `Core/Float.lean`); there is no IEEE-754 library
to state them against independently. `sqrtsSpec e mx a b` is the result, `sqrtsFlags e mx a b` the
exception flags, `sqrtsOk e mx a b` that lean-x86 returns them; lean-x86 computes both with
`Operations.SQRTSf e 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The square root of `b` at MXCSR `mx` in the low element of `a`, the rest of `a` kept. -/
def sqrtsSpec (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : BitVec 128 :=
  fpScalar e a (fpSqrt e mx b).1

/-- The exception flags of the square root. -/
def sqrtsFlags (e : Nat) (mx : BitVec 32) (_a : BitVec 128) (b : BitVec e) : BitVec 6 :=
  (fpSqrt e mx b).2

/-- lean-x86's square root returns a value on `b` (`FpSqrtOk`). -/
def sqrtsOk (e : Nat) (mx : BitVec 32) (_a : BitVec 128) (b : BitVec e) : Prop :=
  FpSqrtOk e mx b

theorem sqrts_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a : BitVec 128) (b : BitVec e) (ctx : Instruction_Context)
    (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s) (hok : sqrtsOk e s.MXCSR a b) :
    (X86.Instructions.Operations.SQRTSf e 128 a b ctx mod).run s =
      (.ok (sqrtsSpec e s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (sqrtsFlags e s.MXCSR a b) }) := by
  rcases he with rfl | rfl <;>
  · unfold X86.Instructions.Operations.SQRTSf
    fp_scalar_sqrt hb hm hok

end X86Proofs
