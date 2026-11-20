import X86Proofs.Core.X87
import X86Proofs.Instructions.Branch.Cond

/-!
# FCMOVcc specification

`FCMOVcc ST(0), ST(i)`: ST(0) := ST(i) if condition `cc` holds of the status flags (FCMOVB `2`,
FCMOVE `4`, FCMOVBE `6`, FCMOVU `A`, FCMOVNB `3`, FCMOVNE `5`, FCMOVNBE `7`, FCMOVNU `B`, the
`Jcc` codes, `condHolds`). lean-x86's `Operations.FCMOV` ORs the status word's exception flags into
themselves (no change), keeps C1 and draws C0, C2, C3 from its oracle; with ST(0) and ST(i) not
empty there is no stack fault.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The status word `Operations.FCMOV` leaves: the exception flags ORed into themselves, C0, C2,
C3 from the oracle `o` (C1 kept). -/
def fcmovStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) : BitVec 16 :=
  setSlice (setSlice (setSlice (fswOrFlags fsw (fsw.extractLsb' 0 6)) 8 1 (oBit o 0)) 10 1
    (oBit o 1)) 14 1 (oBit o 2)

theorem fcmovStatus_eq (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fcmovStatus fsw o = fswSetC fsw (oBit o 0) (fsw.extractLsb' 9 1) (oBit o 1) (oBit o 2) := by
  unfold fcmovStatus
  fsw_bits

@[simp] theorem fswTop_fcmovStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswTop (fcmovStatus fsw o) = fswTop fsw := by
  simp [fcmovStatus_eq]

@[simp] theorem fswES_fcmovStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswES (fcmovStatus fsw o) = fswES fsw := by
  simp [fcmovStatus_eq]

theorem fswRest_fcmovStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswRest (fcmovStatus fsw o) = fswRest fsw := by
  simp [fcmovStatus_eq]

theorem fcmov_operation {σ : Type} (s : X86.State σ) (cc : BitVec 4) (src : BitVec 80)
    (i : BitVec 3) (h0 : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) ≠ 3)
    (hi : ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) ≠ 3)
    (hm : FcwMasked s.FP87_Control) :
    (X86.Instructions.Operations.FCMOV cc src i : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (src, condHolds cc (StatusFlags.ofRFLAGS s.RFLAGS)), { s with
        oracle := oracleSkip s.oracle 3
        FP87_Status := fcmovStatus s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FCMOV
  spec_run [Condition_Holds => conditionHolds_run _ _,
    FP87.Is_STi_Empty => isSTiEmpty_run _ _ (by first | decide | exact unsigned_range _ rfl)]
  have h0' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status) == 3) = false := by simpa using h0
  have hi' : (ftwTag s.FP87_Tag_Word (fswTop s.FP87_Status + i) == 3) = false := by
    simpa using hi
  x87_cond [h0', hi']
  spec_run [X86.FP87_Status.Exception_Flags => fp87StatusFlags_run _,
    FP87.Process_Exceptions => processExceptions_run _ _ (by exact hm),
    X86.UNSPECIFIED => unspecified1_run _]

end X86Proofs
