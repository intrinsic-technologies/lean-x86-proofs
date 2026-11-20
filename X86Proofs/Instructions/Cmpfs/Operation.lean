import X86Proofs.Core.Float

/-!
# CMPSS, CMPSD (compare scalar floats) specification

`CMPSS xmm1, xmm2/m32, imm8` (`F3 0F C2 /r ib`) and `CMPSD xmm1, xmm2/m64, imm8` (`F2 0F C2 /r ib`)
compare the low single- or double-precision elements by the predicate in imm8 bits 0–2 (EQ, LT,
LE, UNORD, NEQ, NLT, NLE, ORD) and write all ones (true) or all zeros (false) to
`DEST[e-1:0]`, `DEST[127:e]` unchanged; the exception flags are ORed into MXCSR. The comparison
and its flags are lean-x86's own `FP.Compare5` at that MXCSR (`fpCompare5`, `Core/Float.lean`);
there is no IEEE-754 library to state them against independently. `cmpfsSpec e mx a b imm` is the
result, `cmpfsFlags e mx a b imm` the exception flags, `cmpfsOk e mx a b imm` that lean-x86
returns them; lean-x86 computes them with `Operations.CMP3Sf e 128 e`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The comparison predicate of a legacy CMPSS/CMPPS: imm8 bits 0–2, zero-extended to 5 bits. -/
def cmpPred (imm : BitVec 8) : BitVec 5 := (0 : BitVec 2) ++ imm.extractLsb' 0 3

/-- A comparison's lane: all ones if it holds, else zero. -/
def cmpMask (e : Nat) (b : Bool) : BitVec e := if b then BitVec.allOnes e else 0

/-- The low element of `a` replaced by the comparison's mask, the rest of `a` kept. -/
def cmpfsSpec (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) (imm : BitVec 8) :
    BitVec 128 :=
  fpScalar e a (cmpMask e (fpCompare5 e (cmpPred imm) mx (a.extractLsb' 0 e) b).1)

/-- The exception flags of the comparison. -/
def cmpfsFlags (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) (imm : BitVec 8) :
    BitVec 6 :=
  (fpCompare5 e (cmpPred imm) mx (a.extractLsb' 0 e) b).2

/-- lean-x86's comparison returns a value on the low elements (`FpCompare5Ok`). -/
def cmpfsOk (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) (imm : BitVec 8) : Prop :=
  FpCompare5Ok e (cmpPred imm) mx (a.extractLsb' 0 e) b

theorem cmpPred_eq (imm : BitVec 8) :
    BitVec.ofNat 5 ((0 : X86.Runtime.Bits 2).toNat <<< 3 + (imm.extractLsb' 0 3).toNat) =
      cmpPred imm := by
  unfold cmpPred
  rw [← ofNat_shiftLeft_add_eq_append_any]

theorem cmpfs_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a : BitVec 128) (b : BitVec e) (imm : BitVec 8) (hm : MxcsrPre s)
    (hok : cmpfsOk e s.MXCSR a b imm) :
    (X86.Instructions.Operations.CMP3Sf e 128 e a b imm).run s =
      (.ok (cmpfsSpec e s.MXCSR a b imm),
        { s with MXCSR := mxOr s.MXCSR (cmpfsFlags e s.MXCSR a b imm) }) := by
  rcases he with rfl | rfl <;>
  · unfold X86.Instructions.Operations.CMP3Sf
    simp (config := { decide := true }) only [x86_runtime, Int.reduceBEq, Bool.true_or,
      Bool.or_true, pure_bind]
    refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
    refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
    rw [cmpPred_eq, extractLsb'_zero_self]
    refine (specM_bind_run _ _ (fpCompare5_run _ (by decide) _ _ _ _ hok)).trans ?_
    unfold cmpfsSpec cmpfsFlags cmpMask
    split <;> rename_i h <;>
      refine (specM_bind_run _ _ (checkExceptions_run _ _ hm)).trans ?_ <;>
      simp only [BitVec.cast_eq] <;> rw [setSlice_scalar _ (by decide)] <;> rfl

end X86Proofs
