import X86Proofs.Core.Float

/-!
# MINPS, MINPD specification

`MINPS xmm1, xmm2/m128` (`0F 5D /r`) and `MINPD xmm1, xmm2/m128` (`66 0F 5D /r`) return
the smaller of the packed single- or double-precision elements lane by lane: `DEST[i] ← IF DEST[i]
< SRC[i] THEN DEST[i] ELSE SRC[i]` (the second operand when either is a NaN or both are zeros)
for every `e`-bit lane (`e` = 32 or 64), with MXCSR's DAZ; every lane's exception flags, reduced
to the invalid one when it is raised (`FP.Prioritize_Operand_Exceptions`, `fpOperandPrio`), are
ORed into MXCSR. Each lane and its flags are lean-x86's own `FP.Min_Max` at that MXCSR
(`fpMinMax`, `Core/Float.lean`); there is no IEEE-754 library to state them against
independently. `minpSpec e mx a b` is the result, `minpFlags e mx a b` the exception flags,
`minpOk e mx a b` that lean-x86 returns every lane; lean-x86 computes both with
`Operations.MINPf e 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Lane `i` of the minimum and its flags (as `FP.Prioritize_Operand_Exceptions` reports them). -/
def minpLane (e : Nat) (mx : BitVec 32) (a b : BitVec 128) (i : Nat) : BitVec e × BitVec 6 :=
  ((fpMinMax e false mx (lane e a i) (lane e b i)).1,
    fpOperandPrio (fpMinMax e false mx (lane e a i) (lane e b i)).2)

/-- The lane-by-lane minimum of `a` and `b` at MXCSR `mx`. -/
def minpSpec (e : Nat) (mx : BitVec 32) (a b : BitVec 128) : BitVec 128 :=
  fpPacked e (minpLane e mx a b)

/-- The exception flags, every lane's ORed. -/
def minpFlags (e : Nat) (mx : BitVec 32) (a b : BitVec 128) : BitVec 6 :=
  fpPackedFlags e (minpLane e mx a b)

/-- lean-x86's operation returns a value on every lane (`FpMinMaxOk`). -/
def minpOk (e : Nat) (mx : BitVec 32) (a b : BitVec 128) : Prop :=
  ∀ i < 128 / e, FpMinMaxOk e false mx (lane e a i) (lane e b i)

theorem minp_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a b : BitVec 128) (hm : MxcsrPre s) (hok : minpOk e s.MXCSR a b) :
    (X86.Instructions.Operations.MINPf e 128 a b).run s =
      (.ok (minpSpec e s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (minpFlags e s.MXCSR a b) }) := by
  rcases he with rfl | rfl <;> unfold X86.Instructions.Operations.MINPf <;> fp_packed_start_minmax
  · fp_packed_loop 32 (fun i hi => fpMinMax_run _ (by decide) _ _ _ _ (hok i hi)) hm masked
  · fp_packed_loop 64 (fun i hi => fpMinMax_run _ (by decide) _ _ _ _ (hok i hi)) hm masked

end X86Proofs
