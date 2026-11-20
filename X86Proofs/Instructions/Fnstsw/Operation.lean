import X86Proofs.Instructions.Fnop.Operation

/-!
# FNSTSW specification

`FNSTSW AX`, `FNSTSW m16`: AX or the memory word := the x87 status word, without checking for a
pending exception. lean-x86's `Operations.FNSTSW` returns the status word as it was, then draws
all four condition codes from its oracle (the SDM leaves them undefined after the store).
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

theorem fnstsw_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.FNSTSW true : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok s.FP87_Status, { s with
        oracle := oracleSkip s.oracle 4
        FP87_Status := fswCCOracle s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FNSTSW FP87.Synchronize
  spec_run [MonadState.get => specM_get_run _, X86.UNSPECIFIED => unspecified1_run _]

theorem fnstsw_m_operation {σ : Type} (s : X86.State σ) :
    (X86.Instructions.Operations.FNSTSW false : SpecM X86.Exception (X86.State σ) _).run s =
      (.ok s.FP87_Status, { s with
        oracle := oracleSkip s.oracle 4
        FP87_Status := fswCCOracle s.FP87_Status s.oracle }) := by
  unfold X86.Instructions.Operations.FNSTSW
  spec_run [MonadState.get => specM_get_run _, X86.UNSPECIFIED => unspecified1_run _]

end X86Proofs
