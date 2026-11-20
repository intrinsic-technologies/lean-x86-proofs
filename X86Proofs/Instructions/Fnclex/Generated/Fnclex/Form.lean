import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fnclex.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fnclex_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) :
    (X86.Instructions.FNCLEX ip ctx).run s =
      (.ok (), x87CtlOut s ip 4 (fnclexStatus s.FP87_Status s.oracle)) := by
  unfold X86.Instructions.FNCLEX
  simp only [hlock]
  spec_run [FP87.Is_Enabled => isEnabled_run hcr0,
    X86.Instructions.Operations.FNCLEX => fnclex_operation _]

end X86Proofs
