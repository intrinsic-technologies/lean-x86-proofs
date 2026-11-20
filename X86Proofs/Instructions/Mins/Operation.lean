import X86Proofs.Core.Float

/-!
# MINSS, MINSD specification

`MINSS xmm1, xmm2/m32` (`F3 0F 5D /r`) and `MINSD xmm1, xmm2/m64` (`F2 0F 5D /r`) return the smaller
of the low single- or double-precision elements: `DEST[e-1:0] ← IF DEST < SRC THEN DEST ELSE SRC`
(the second operand when either is a NaN or both are zeros), `DEST[127:e]` unchanged (`e` = 32 or
64), with MXCSR's DAZ, and the exception flags ORed into MXCSR. The minimum and its flags are
lean-x86's own `FP.Min_Max` at that MXCSR (`fpMinMax`, `Core/Float.lean`); there is no IEEE-754
library to state them against independently. `minsSpec e mx a b` is the result, `minsFlags e mx a b`
the exception flags, `minsOk e mx a b` that lean-x86 returns them; lean-x86 computes both with
`Operations.MINSf e 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The minimum of the low elements of `a` and `b` at MXCSR `mx`, the rest of `a` kept. -/
def minsSpec (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : BitVec 128 :=
  fpScalar e a (fpMinMax e false mx (a.extractLsb' 0 e) b).1

/-- The exception flags of the operation. -/
def minsFlags (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : BitVec 6 :=
  (fpMinMax e false mx (a.extractLsb' 0 e) b).2

/-- lean-x86's operation returns a value on the low elements (`FpMinMaxOk`). -/
def minsOk (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : Prop :=
  FpMinMaxOk e false mx (a.extractLsb' 0 e) b

theorem mins_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a : BitVec 128) (b : BitVec e) (hm : MxcsrPre s)
    (hok : minsOk e s.MXCSR a b) :
    (X86.Instructions.Operations.MINSf e 128 a b).run s =
      (.ok (minsSpec e s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (minsFlags e s.MXCSR a b) }) := by
  rcases he with rfl | rfl <;>
  · unfold X86.Instructions.Operations.MINSf
    fp_scalar_minmax hm hok

end X86Proofs
