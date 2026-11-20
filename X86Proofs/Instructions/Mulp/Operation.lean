import X86Proofs.Core.Float

/-!
# MULPS, MULPD specification

`MULPS xmm1, xmm2/m128` (`0F 59 /r`) and `MULPD xmm1, xmm2/m128` (`66 0F 59 /r`) multiply the packed
single- or double-precision elements lane by lane: `DEST[i] ← DEST[i] * SRC[i]` for every `e`-bit
lane (`e` = 32 or 64), rounded as MXCSR.RC says, with MXCSR's DAZ and FTZ; the exception flags of
every lane are ORed into MXCSR. There is no IEEE-754 library to state the products against
independently, so each lane and its flags are lean-x86's own `FP.Arithmetic FP_MUL` at that MXCSR
(`fpArith`, `Core/Float.lean`). `mulpSpec e mx a b` is the result, `mulpFlags e mx a b` the
exception flags, `mulpOk e mx a b` that lean-x86 returns every lane; lean-x86 computes both with
`Operations.MULPf e 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the product and its flags. -/
def mulpLane (e : Nat) (mx : BitVec 32) (a b : BitVec 128) (i : Nat) : BitVec e × BitVec 6 :=
  fpArith e .FP_MUL mx (lane e a i) (lane e b i)

/-- The lane-by-lane product of `a` and `b` at MXCSR `mx`. -/
def mulpSpec (e : Nat) (mx : BitVec 32) (a b : BitVec 128) : BitVec 128 :=
  fpPacked e (mulpLane e mx a b)

/-- The exception flags, every lane's ORed. -/
def mulpFlags (e : Nat) (mx : BitVec 32) (a b : BitVec 128) : BitVec 6 :=
  fpPackedFlags e (mulpLane e mx a b)

/-- lean-x86's operation returns a value on every lane (`FpArithOk`). -/
def mulpOk (e : Nat) (mx : BitVec 32) (a b : BitVec 128) : Prop :=
  ∀ i < 128 / e, FpArithOk e .FP_MUL mx (lane e a i) (lane e b i)

theorem mulp_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a b : BitVec 128) (ctx : Instruction_Context)
    (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s) (hok : mulpOk e s.MXCSR a b) :
    (X86.Instructions.Operations.MULPf e 128 a b ctx mod).run s =
      (.ok (mulpSpec e s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (mulpFlags e s.MXCSR a b) }) := by
  rcases he with rfl | rfl <;> unfold X86.Instructions.Operations.MULPf <;> fp_packed_start hb
  · fp_packed_loop 32 (fun i hi => fpArith_run _ (by decide) _ _ _ _ (hok i hi)) hm
  · fp_packed_loop 64 (fun i hi => fpArith_run _ (by decide) _ _ _ _ (hok i hi)) hm

end X86Proofs
