import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Std.Operation

namespace X86Proofs

open X86 X86.Machine X86.Helpers

theorem std_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.STD ip ctx).run s =
      (.ok (), writeResult s (Operand.df : Operand 1) stdSpec ip) := by
  have hcontext : {ctx with lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.STD
  simp only [writeResult]
  spec_run [X86.Instructions.Operations.STD => std_operation _]

end X86Proofs
