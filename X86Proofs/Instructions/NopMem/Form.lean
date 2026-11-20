import X86Proofs.Step.Address
import X86Proofs.Instructions.Nop.Form

/-!
# Layer 2: `NOP_MEMv_0F1F` (`0F 1F /0` with a memory operand)

lean-x86's `NOP_MEMv_0F1F` runs `Effective_Address` only to fetch the SIB and displacement bytes
and find `Next_IP`; it drops the offset and segment, so nothing is read or translated and the
address cannot fault. Then it checks for a LOCK prefix and sets `Next_IP`: the result is
`withNextIP t next`, `t` the state after the address bytes are fetched.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `NOP_MEMv_0F1F`. With address size 64 and no LOCK prefix: if the address computation
returns `next` (the address after the displacement) and leaves state `t`, the form succeeds and
only sets `Next_IP := next` in `t`.
-/
theorem nop_m_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (off next : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t)) :
    (X86.Instructions.NOP_MEMv_0F1F ip ctx mod rm).run s = (.ok (), withNextIP t next) := by
  unfold X86.Instructions.NOP_MEMv_0F1F
  rw [haddr]
  refine (specM_bind_run _ _ hea).trans ?_
  simp [hlock]
  rfl

end X86Proofs
