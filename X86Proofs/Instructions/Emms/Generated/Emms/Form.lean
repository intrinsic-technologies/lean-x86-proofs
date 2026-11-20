import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Instructions.Emms.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem emms_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) (hes : fswES s.FP87_Status = 0)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) :
    (X86.Instructions.EMMS ip ctx).run s =
      (.ok (), { s with
        Next_IP := ip
        FP87_Tag_Word := emmsSpec
        FP87_Status := mmxStatus s.FP87_Status }) := by
  unfold X86.Instructions.EMMS
  simp only [hrep, hlock, hosz]
  spec_run [
    X86.CR0.EM => cr0EM_run_of_cr0 hcr0,
    X86.CR0.TS => cr0TS_run_of_cr0 hcr0,
    FP87.Check_For_Pending_Unmasked_Floating_Point_Exceptions => checkPending_run _ hes,
    X86.Instructions.Operations.EMMS => emms_operation _]

end X86Proofs
