import X86Proofs.Core.Operand
import X86Proofs.Instructions.Stc.Operation

namespace X86Proofs

open X86 X86.Helpers

theorem stc_form {σ : Type} (s : X86.State σ) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.STC ip ctx).run s =
      (.ok (), writeFlagsOutputs s (stcSpec (StatusFlags.ofRFLAGS s.RFLAGS)) 0 ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.STC
  simp only [writeFlagsOutputs, oracleSkip_zero]
  spec_run [X86.Instructions.Operations.STC => stc_operation _]

end X86Proofs
