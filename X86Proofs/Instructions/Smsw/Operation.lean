import X86Proofs.Step.Address

/-!
# SMSW specification

`SMSW r/m` (`0F 01 /4`, Intel SDM): `DEST ← CR0[15:0]`; with a register destination at operand size
32 or 64 the high bits are those of CR0 (lean-x86: `CR0[0 +: n]`), a memory destination is 16 bits.
Outside VMX non-root operation (where lean-x86 reads the CR0 read shadow instead) the value is the
low `n` bits of CR0, `smswSpec n cr0`.
-/

namespace X86Proofs

/-- The value `SMSW` writes at operand size `n`: the low `n` bits of CR0. -/
def smswSpec (n : Nat) (cr0 : BitVec 64) : BitVec n := cr0.setWidth n

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem smsw_operation (s : RamState) (n : Nat) (hn : n = 64 ∨ n = 32 ∨ n = 16)
    (hvmx : s.VMX_Operation_Mode ≠ VMX_Operation_Type.VMX_Non_Root) :
    (X86.Instructions.Operations.SMSW n).run s = (.ok (smswSpec n s.CR0), s) := by
  have hb : (s.VMX_Operation_Mode == VMX_Operation_Type.VMX_Non_Root) = false := by
    simpa using hvmx
  unfold X86.Instructions.Operations.SMSW
  rcases hn with rfl | rfl | rfl <;>
  · spec_run [MonadState.get => get_run _]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    spec_run [MonadState.get => get_run _]
    try simp [smswSpec, x86_runtime, X86.Runtime.CheckedSlice.read]

end X86Proofs
