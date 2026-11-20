import X86Proofs.Core.Run
import X86Proofs.Core.Operand

namespace X86Proofs

open X86 X86.Helpers

theorem nop_18r7_r_form {σ : Type} (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.NOP_GPRv_0F18r7 ip ctx).run s = (.ok (), withNextIP s ip) := by
  simp [X86.Instructions.NOP_GPRv_0F18r7, hlock]
  rfl

end X86Proofs
