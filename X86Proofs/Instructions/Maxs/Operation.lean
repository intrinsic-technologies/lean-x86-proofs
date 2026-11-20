import X86Proofs.Core.Float

/-!
# MAXSS, MAXSD specification

`MAXSS xmm1, xmm2/m32` (`F3 0F 5F /r`) and `MAXSD xmm1, xmm2/m64` (`F2 0F 5F /r`) return the larger
of the low single- or double-precision elements: `DEST[e-1:0] ← IF DEST > SRC THEN DEST ELSE SRC`
(the second operand when either is a NaN or both are zeros), `DEST[127:e]` unchanged (`e` = 32 or
64), with MXCSR's DAZ, and the exception flags ORed into MXCSR. The maximum and its flags are
lean-x86's own `FP.Min_Max` at that MXCSR (`fpMinMax`, `Core/Float.lean`); there is no IEEE-754
library to state them against independently. `maxsSpec e mx a b` is the result, `maxsFlags e mx a b`
the exception flags, `maxsOk e mx a b` that lean-x86 returns them; lean-x86 computes both with
`Operations.MAXSf e 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The maximum of the low elements of `a` and `b` at MXCSR `mx`, the rest of `a` kept. -/
def maxsSpec (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : BitVec 128 :=
  fpScalar e a (fpMinMax e true mx (a.extractLsb' 0 e) b).1

/-- The exception flags of the operation. -/
def maxsFlags (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : BitVec 6 :=
  (fpMinMax e true mx (a.extractLsb' 0 e) b).2

/-- lean-x86's operation returns a value on the low elements (`FpMinMaxOk`). -/
def maxsOk (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : Prop :=
  FpMinMaxOk e true mx (a.extractLsb' 0 e) b

theorem maxs_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a : BitVec 128) (b : BitVec e) (hm : MxcsrPre s)
    (hok : maxsOk e s.MXCSR a b) :
    (X86.Instructions.Operations.MAXSf e 128 a b).run s =
      (.ok (maxsSpec e s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (maxsFlags e s.MXCSR a b) }) := by
  rcases he with rfl | rfl <;>
  · unfold X86.Instructions.Operations.MAXSf
    fp_scalar_minmax hm hok

end X86Proofs
