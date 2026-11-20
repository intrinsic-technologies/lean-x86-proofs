import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fninit.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fninit_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) :
    (X86.Instructions.FNINIT ip ctx).run s =
      (.ok (), x87InitOut s ip (fninitControl s.FP87_Control)) := by
  unfold X86.Instructions.FNINIT
  simp only [hlock]
  spec_run [FP87.Is_Enabled => isEnabled_run hcr0,
    X86.Instructions.Operations.FNINIT => fninit_operation _]

end X86Proofs
