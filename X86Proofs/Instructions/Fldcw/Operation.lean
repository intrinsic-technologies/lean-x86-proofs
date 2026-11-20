import X86Proofs.Instructions.Fnop.Operation
import X86.Instructions.FLDCW

/-!
# FLDCW specification

`FLDCW m16`: the control word := the word loaded, with its reserved bits fixed (bit 6 set, bits 7
and 13–15 clear: `fldcwWord`); the condition codes are undefined (lean-x86 draws all four from its
oracle). lean-x86 then processes the status word's sticky exception flags against the new control
word (`FP87.Process_Exceptions`): with every exception masked by the new word, nothing changes.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

/-- The control word FLDCW loads from `v`: bit 6 set, bits 7 and 13–15 clear. -/
def fldcwWord (v : BitVec 16) : BitVec 16 :=
  FP87_Control_Type.setRESERVED_ZERO (setSlice v 6 1 1) 0

theorem fswOrFlags_flags (f : BitVec 16) : fswOrFlags f (f.extractLsb' 0 6) = f := by
  unfold fswOrFlags
  fsw_bits

theorem fldcw_operation {σ : Type} (s : X86.State σ) (v : BitVec 16)
    (hm : FcwMasked (fldcwWord v)) :
    (X86.Instructions.Operations.FLDCW v : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        FP87_Control := fldcwWord v
        oracle := oracleSkip s.oracle 4
        FP87_Status := fswCCOracle s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FLDCW
  spec_run_until [X86.UNSPECIFIED => unspecified1_run _,
    X86.FP87_Status.Exception_Flags => fp87StatusFlags_run _]
  dsimp only
  refine (processExceptions_run _ _ ?_).trans ?_
  · exact hm
  simp only [fswOrFlags_flags]
  rfl

end X86Proofs
