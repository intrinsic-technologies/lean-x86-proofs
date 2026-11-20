import X86Proofs.Core.Operand
import X86Proofs.Instructions.Cmc.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem cmc_form {σ : Type} (s : X86.State σ) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.CMC ip ctx).run s =
      (.ok (), writeFlagsOutputs s (cmcSpec (StatusFlags.ofRFLAGS s.RFLAGS)) 0 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.CMC
  simp only [writeFlagsOutputs, oracleSkip_zero]
  spec_run [X86.Instructions.Operations.CMC => cmc_operation _]

end X86Proofs
