import X86Proofs.Program.ReadWrite.X87
import X86Proofs.Instructions.Fnop.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem fsetpm_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0) :
    (X86.Instructions.FSETPM287_NOP ip ctx).run s =
      (.ok (), withNextIP s ip) := by
  unfold X86.Instructions.FSETPM287_NOP
  exact obsoleteX87Nop_run _ _ _ hlock hcr0

end X86Proofs
