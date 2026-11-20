import X86Proofs.Step.Address

/-!
# Encoding CALL

The standard bytes of `call rel32` (`E8`), `call r64` (`FF /2`, register) and `call [mem]`
(`FF /2`, memory, any `AddrMode`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The bytes of `call rel32` with displacement `disp`: `E8` and the displacement. -/
def encodeCallRel32 (disp : BitVec 32) : List UInt8 := 0xE8 :: immBytes 32 disp

/-- The bytes of `call r` for the 64-bit register numbered `r` (0–15): `FF` and ModRM
`11 010 r&7`, after `41` (REX.B) if `r` is 8–15. E.g. `encodeCallR64 13 = [0x41, 0xFF, 0xD5]`. -/
def encodeCallR64 (r : BitVec 4) : List UInt8 :=
  if r.toNat < 8 then [0xFF, UInt8.ofNat (0xD0 + r.toNat)]
  else [0x41, 0xFF, UInt8.ofNat (0xD0 + r.toNat % 8)]

/-- `encodeCallR64` is a valid encoding of the register it names. -/
theorem encodeCallR64_spec (r : BitVec 4) :
    (∃ modrm, encodeCallR64 r = [0xFF, modrm] ∧ modrmMod modrm = 3 ∧ modrmReg modrm = 2 ∧
      gprNumber 0 0 (modrmRm modrm) = r.setWidth 5) ∨
    (∃ rex modrm, encodeCallR64 r = [rex, 0xFF, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = 2 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = r.setWidth 5) := by
  by_cases hlow : r.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert r
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert r
    decide

/-- The bytes of `call qword [am]` with no prefix: `FF`, ModRM with `reg = 2`, then `am.tail`
(the address must need no REX bit). E.g. `encodeCallM64 (.rip d)` is `FF 15 d32`. -/
def encodeCallM64 (am : AddrMode) : List UInt8 := 0xFF :: am.modrm 2 :: am.tail

end X86Proofs
