import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fwait.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fwait_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES s.FP87_Status = 0) :
    (X86.Instructions.FWAIT ip ctx).run s =
      (.ok (), x87CtlOut s ip 4 (fswCCOracle s.FP87_Status s.oracle)) := by
  unfold X86.Instructions.FWAIT
  simp only [hlock]
  spec_run_until [X86.CR0.MP => cr0MP_run _, X86.CR0.TS => cr0TS_run_of_cr0 hcr0]
  x87_cond [show ((0 : BitVec 1) == 1) = false from rfl]
  spec_run [FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.Instructions.Operations.FWAIT => fwait_operation _ (by exact hes)]

end X86Proofs
