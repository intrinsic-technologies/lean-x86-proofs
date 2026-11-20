import X86Proofs.Core.X87Arith

/-!
# FTST specification

lean-x86's `Operations.FTST x`, with ST(0) not empty and every exception masked: C0, C2, C3 := the
comparison of `x` with +0.0 (`x87Compare`, ordered), C1 := 0, its exception flags ORed into the
status word (`x87CmpFsw`).
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers X86.Runtime

theorem ftst_operation (s : RamState) (x : BitVec 80)
    (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hm : FcwMasked s.FP87_Control) (hok : X87CompareOk true x 0) :
    (X86.Instructions.Operations.FTST x : SpecM X86.Exception RamState _).run s =
      (.ok (), { s with
        FP87_Status := x87CmpFsw s.FP87_Status (x87Compare true x 0).1
          (x87Compare true x 0).2 }) := by
  unfold X86.Instructions.Operations.FTST
  spec_run_until [FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by decide)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  x87_cond [h0']
  spec_run_until []
  rw [show F80_Type.setSign (0 : BitVec 80) 0 = 0 from rfl, hok.eq]
  spec_run [FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm)]

end X86Proofs
