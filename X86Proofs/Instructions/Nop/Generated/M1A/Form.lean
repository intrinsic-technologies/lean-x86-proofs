import X86Proofs.Step.Address
import X86Proofs.Instructions.Nop.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem nop_1a_m_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (off next : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t)) :
    (X86.Instructions.NOP_MEMv_GPRv_0F1A ip ctx mod rm).run s = (.ok (), withNextIP t next) := by
  unfold X86.Instructions.NOP_MEMv_GPRv_0F1A
  rw [haddr]
  refine (specM_bind_run _ _ hea).trans ?_
  simp [hlock]
  rfl

end X86Proofs
