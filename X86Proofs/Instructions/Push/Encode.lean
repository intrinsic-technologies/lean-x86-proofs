import X86Proofs.Step.Address
import X86Proofs.Instructions.Push.Decode

/-!
# Encoding `push r64`

The standard bytes of `push r64` (`50+r`, after `41` for R8–R15) and that they name the register.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/--
The bytes of `push src` for the 64-bit register numbered `src` (0–15), in the shortest encoding:
opcode `50 + (src & 7)`, after a REX prefix `41` (REX.B) if `src` is 8–15. E.g.
`encodePushR64 5 = [0x55]` (`push rbp`), `encodePushR64 15 = [0x41, 0x57]` (`push r15`).
-/
def encodePushR64 (src : BitVec 4) : List UInt8 :=
  if src.toNat < 8 then [UInt8.ofNat (0x50 + src.toNat)]
  else [0x41, UInt8.ofNat (0x50 + src.toNat % 8)]

/-- `encodePushR64` is a valid encoding of the register it names. -/
theorem encodePushR64_spec (src : BitVec 4) :
    (∃ op, encodePushR64 src = [op] ∧ PushOpcode op ∧
      gprNumber 0 0 (opcodeReg op) = src.setWidth 5) ∨
    (∃ rex op, encodePushR64 src = [rex, op] ∧ RexPrefix rex.toBitVec ∧ PushOpcode op ∧
      gprNumber 0 (rexB rex.toBitVec) (opcodeReg op) = src.setWidth 5) := by
  by_cases hlow : src.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert src
    decide

end X86Proofs
