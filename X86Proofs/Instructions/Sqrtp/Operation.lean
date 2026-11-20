import X86Proofs.Core.Float

/-!
# SQRTPS, SQRTPD specification

`SQRTPS xmm1, xmm2/m128` (`0F 51 /r`) and `SQRTPD xmm1, xmm2/m128` (`66 0F 51 /r`) take the square
root of the packed single- or double-precision elements of the source lane by lane: `DEST[i] ←
SQRT(SRC[i])` for every `e`-bit lane (`e` = 32 or 64), rounded as MXCSR.RC says, with MXCSR's DAZ
and FTZ; the exception flags of every lane are ORed into MXCSR. Each lane and its flags are
lean-x86's own `FP.Sqrt` at that MXCSR (`fpSqrt`, `Core/Float.lean`); there is no IEEE-754
library to state them against independently. `sqrtpSpec e mx a b` is the result (the destination
`a` is not read), `sqrtpFlags e mx a b` the exception flags, `sqrtpOk e mx a b` that lean-x86
returns every lane; lean-x86 computes both with `Operations.SQRTPf e 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the square root and its flags. -/
def sqrtpLane (e : Nat) (mx : BitVec 32) (b : BitVec 128) (i : Nat) : BitVec e × BitVec 6 :=
  fpSqrt e mx (lane e b i)

/-- The lane-by-lane square root of `b` at MXCSR `mx`. -/
def sqrtpSpec (e : Nat) (mx : BitVec 32) (_a b : BitVec 128) : BitVec 128 :=
  fpPacked e (sqrtpLane e mx b)

/-- The exception flags, every lane's ORed. -/
def sqrtpFlags (e : Nat) (mx : BitVec 32) (_a b : BitVec 128) : BitVec 6 :=
  fpPackedFlags e (sqrtpLane e mx b)

/-- lean-x86's square root returns a value on every lane (`FpSqrtOk`). -/
def sqrtpOk (e : Nat) (mx : BitVec 32) (_a b : BitVec 128) : Prop :=
  ∀ i < 128 / e, FpSqrtOk e mx (lane e b i)

theorem sqrtp_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a b : BitVec 128) (ctx : Instruction_Context)
    (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s) (hok : sqrtpOk e s.MXCSR a b) :
    (X86.Instructions.Operations.SQRTPf e 128 b ctx mod).run s =
      (.ok (sqrtpSpec e s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (sqrtpFlags e s.MXCSR a b) }) := by
  rcases he with rfl | rfl <;> unfold X86.Instructions.Operations.SQRTPf <;> fp_packed_start_sqrt hb
  · fp_packed_loop 32 (fun i hi => fpSqrt_run _ (by decide) _ _ (hok i hi)) hm
  · fp_packed_loop 64 (fun i hi => fpSqrt_run _ (by decide) _ _ (hok i hi)) hm

end X86Proofs
