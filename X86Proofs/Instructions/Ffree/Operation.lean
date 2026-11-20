import X86Proofs.Core.X87

/-!
# FFREE specification

`FFREE ST(i)`: tag ST(i) empty; TOP and the registers are unchanged. lean-x86's
`Operations.FFREE` then leaves C1 := 0 and draws C0, C2, C3 from its oracle. `FFREEP ST(i)` (`DF
C0+i`) also pops.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

theorem ffree_operation {σ : Type} (s : X86.State σ) (i : BitVec 3) :
    (X86.Instructions.Operations.FFREE i : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        oracle := oracleSkip s.oracle 3
        FP87_Tag_Word := ftwSet s.FP87_Tag_Word (fswTop s.FP87_Status + i) 3
        FP87_Status := fswC1Zero s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FFREE
  spec_run [FP87.Free => free_run _ _ i (unsigned_eq i), X86.UNSPECIFIED => unspecified1_run _]

end X86Proofs
