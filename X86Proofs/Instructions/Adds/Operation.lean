import X86Proofs.Core.Float

/-!
# ADDSS, ADDSD specification

`ADDSS xmm1, xmm2/m32` (`F3 0F 58 /r`) and `ADDSD xmm1, xmm2/m64` (`F2 0F 58 /r`) add the low
single- or double-precision elements: `DEST[e-1:0] ← DEST[e-1:0] + SRC[e-1:0]`, `DEST[127:e]`
unchanged (`e` = 32 or 64), rounded as MXCSR.RC says, with MXCSR's DAZ and FTZ, and the exception
flags it raises ORed into MXCSR. There is no IEEE-754 library to state the sum against
independently, so the sum and its flags are lean-x86's own `FP.Arithmetic FP_ADD` at that MXCSR
(`fpArith`, `Core/Float.lean`). `addsSpec e mx a b` is the result, `addsFlags e mx a b` the
exception flags, `addsOk e mx a b` that lean-x86 returns them; lean-x86 computes both with
`Operations.ADDSf e 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The low element of `a` plus `b` at MXCSR `mx`, the rest of `a` kept. -/
def addsSpec (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : BitVec 128 :=
  fpScalar e a (fpArith e .FP_ADD mx (a.extractLsb' 0 e) b).1

/-- The exception flags of the addition. -/
def addsFlags (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : BitVec 6 :=
  (fpArith e .FP_ADD mx (a.extractLsb' 0 e) b).2

/-- lean-x86's addition returns a value on the low elements (`FpArithOk`). -/
def addsOk (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : Prop :=
  FpArithOk e .FP_ADD mx (a.extractLsb' 0 e) b

theorem adds_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a : BitVec 128) (b : BitVec e) (ctx : Instruction_Context)
    (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s)
    (hok : addsOk e s.MXCSR a b) :
    (X86.Instructions.Operations.ADDSf e 128 a b ctx mod).run s =
      (.ok (addsSpec e s.MXCSR a b),
        { s with MXCSR := mxOr s.MXCSR (addsFlags e s.MXCSR a b) }) := by
  rcases he with rfl | rfl <;>
  · unfold X86.Instructions.Operations.ADDSf
    fp_scalar_arith hb hm hok

end X86Proofs
