import X86Proofs.Core.Run
import X86Proofs.Core.Operand

/-!
# Layer 2: NOP forms

`NOP_90` (`90`, and `66 90`) and `NOP_GPRv_0F1F` (`0F 1F /0` with a register operand) only check
for a LOCK prefix and set `Next_IP`: the result is `withNextIP s ip` (`Core/Operand.lean`). (The memory form
`NOP_MEMv_0F1F` also parses the ModRM/SIB address bytes to find `Next_IP`.)
-/

namespace X86Proofs

open X86 X86.Helpers

/-- Layer 2 for `NOP_90`: without a LOCK prefix it succeeds and only sets `Next_IP`. -/
theorem nop_form {σ : Type} (s : X86.State σ) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.NOP_90 ip ctx).run s = (.ok (), withNextIP s ip) := by
  simp [X86.Instructions.NOP_90, hlock]
  rfl

/-- Layer 2 for `NOP_GPRv_0F1F`: without a LOCK prefix it succeeds and only sets `Next_IP`. -/
theorem nop_r_form {σ : Type} (s : X86.State σ) (ip : BitVec 64)
    (ctx : Instruction_Context) (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.NOP_GPRv_0F1F ip ctx).run s = (.ok (), withNextIP s ip) := by
  simp [X86.Instructions.NOP_GPRv_0F1F, hlock]
  rfl

end X86Proofs
