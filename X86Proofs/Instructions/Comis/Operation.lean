import X86Proofs.Core.Float

/-!
# COMISS, COMISD specification

`COMISS xmm1, xmm2/m32` (`NP 0F 2F /r`) and `COMISD xmm1, xmm2/m64` (`66 0F 2F /r`) compare the low
single- or double-precision elements and set ZF, PF, CF: unordered (a NaN operand) 1, 1, 1;
greater 0, 0, 0; less 0, 0, 1; equal 1, 0, 0; and clear OF, SF, AF. A QNaN or SNaN operand raises
the invalid exception (a signalling comparison); the exception flags are ORed into MXCSR. The
comparison and its flags are lean-x86's own `FP.Compare` (signalling) at that MXCSR (`fpCompare`,
`Core/Float.lean`); there is no IEEE-754 library to state them against independently.
`comisFlags e mx a b` are the status flags, `comisExc e mx a b` the exception flags, `comisOk e mx a
b` that lean-x86 returns them; lean-x86 computes them with `Operations.COMISf e 128`.
-/

namespace X86Proofs

open X86 X86.Helpers

/-- The status flags of the comparison: ZF, PF, CF from the comparison, OF, SF, AF clear. -/
def comisFlags (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : StatusFlags :=
  fpCompareFlags (fpCompare e true mx (a.extractLsb' 0 e) b).1

/-- The exception flags of the comparison. -/
def comisExc (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : BitVec 6 :=
  (fpCompare e true mx (a.extractLsb' 0 e) b).2

/-- lean-x86's comparison returns a value on the low elements (`FpCompareOk`). -/
def comisOk (e : Nat) (mx : BitVec 32) (a : BitVec 128) (b : BitVec e) : Prop :=
  FpCompareOk e true mx (a.extractLsb' 0 e) b

theorem comis_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a : BitVec 128) (b : BitVec e) (ctx : Instruction_Context)
    (mod : BitVec 2) (hb : ctx.evex_b = 0) (hm : MxcsrPre s) (hok : comisOk e s.MXCSR a b) :
    (X86.Instructions.Operations.COMISf e 128 a b ctx mod).run s =
      (.ok (), setFlags { s with MXCSR := mxOr s.MXCSR (comisExc e s.MXCSR a b) }
        (comisFlags e s.MXCSR a b)) := by
  rcases he with rfl | rfl <;>
  · unfold X86.Instructions.Operations.COMISf
    simp (config := { decide := true }) only [x86_runtime, hb, Int.reduceBEq, Bool.true_or,
      pure_bind, BitVec.reduceBEq]
    refine (specM_bind_run _ _ (getDAZ_run _ (by decide) _)).trans ?_
    refine (specM_bind_run _ _ (mxcsrMasks_run _)).trans ?_
    simp only [and_false_left, Bool.false_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (fpCompare_run _ (by decide) _ _ _ _ hok)).trans ?_
    refine (specM_bind_run _ _ (checkExceptions_run _ _ hm)).trans ?_
    exact compareRflags_run _ _

end X86Proofs
