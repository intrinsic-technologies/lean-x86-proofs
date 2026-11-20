import X86Proofs.Step.Address
import X86Proofs.Instructions.Pop.Decode

/-!
# Encoding `pop r64`

The standard bytes of `pop r64` (`58+r`, after `41` for R8–R15) and that they name the register.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/--
The bytes of `pop dst` for the 64-bit register numbered `dst` (0–15), in the shortest encoding:
opcode `58 + (dst & 7)`, after a REX prefix `41` (REX.B) if `dst` is 8–15. E.g.
`encodePopR64 5 = [0x5D]` (`pop rbp`), `encodePopR64 15 = [0x41, 0x5F]` (`pop r15`).
-/
def encodePopR64 (dst : BitVec 4) : List UInt8 :=
  if dst.toNat < 8 then [UInt8.ofNat (0x58 + dst.toNat)]
  else [0x41, UInt8.ofNat (0x58 + dst.toNat % 8)]

/-- `encodePopR64` is a valid encoding of the register it names. -/
theorem encodePopR64_spec (dst : BitVec 4) :
    (∃ op, encodePopR64 dst = [op] ∧ PopOpcode op ∧
      gprNumber 0 0 (opcodeReg op) = dst.setWidth 5) ∨
    (∃ rex op, encodePopR64 dst = [rex, op] ∧ RexPrefix rex.toBitVec ∧ PopOpcode op ∧
      gprNumber 0 (rexB rex.toBitVec) (opcodeReg op) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert dst
    decide

end X86Proofs
