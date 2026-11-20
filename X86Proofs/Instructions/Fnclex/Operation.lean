import X86Proofs.Core.X87

/-!
# FNCLEX specification

`FNCLEX`: clears the exception flags (bits 0–5), SF, ES and B of the x87 status word, without
checking for a pending exception; TOP is kept. lean-x86's `Operations.FNCLEX` draws all four
condition codes from its oracle (the SDM leaves them undefined).
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- The status word FNCLEX leaves, bit by bit as lean-x86 sets it (`fnclexStatus_eq`: TOP kept,
every other bit but the condition codes cleared, C0, C1, C2, C3 the oracle's next four bits). -/
def fnclexStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) : BitVec 16 :=
  setSlice (setSlice (setSlice (setSlice (setSlice (setSlice (setSlice (setSlice (setSlice
    (setSlice (setSlice (setSlice (setSlice fsw 0 1 0) 1 1 0) 2 1 0) 3 1 0) 4 1 0) 5 1 0) 6 1 0)
    7 1 0) 8 1 (oBit o 0)) 9 1 (oBit o 1)) 10 1 (oBit o 2)) 14 1 (oBit o 3)) 15 1 0

theorem fnclexStatus_eq (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fnclexStatus fsw o =
      fswSetC (fsw &&& 0x3800#16) (oBit o 0) (oBit o 1) (oBit o 2) (oBit o 3) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt16_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp [fnclexStatus, fswSetC, getElem_setSlice]

@[simp] theorem fswTop_fnclexStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswTop (fnclexStatus fsw o) = fswTop fsw := by
  rw [fnclexStatus_eq, fswTop_fswSetC]
  simp only [fswTop]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp

@[simp] theorem fswES_fnclexStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswES (fnclexStatus fsw o) = 0 := by
  rw [fnclexStatus_eq, fswES_fswSetC]
  simp only [fswES]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and]
  rcases (by omega : i = 0) with rfl
  simp

theorem fswRest_fnclexStatus (fsw : BitVec 16) (o : X86.Runtime.Oracle) :
    fswRest (fnclexStatus fsw o) = fsw &&& 0x3800#16 := by
  rw [fnclexStatus_eq, fswRest_fswSetC]
  simp only [fswRest]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt16_cases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp

theorem fswRest_and_3800 (fsw : BitVec 16) : fswRest fsw &&& 0x3800#16 = fsw &&& 0x3800#16 := by
  simp only [fswRest, BitVec.and_assoc]
  rfl

theorem fnclex_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.FNCLEX : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok (), { s with
        oracle := oracleSkip s.oracle 4
        FP87_Status := fnclexStatus s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FNCLEX
  spec_run [X86.UNSPECIFIED => unspecified1_run _]

end X86Proofs
