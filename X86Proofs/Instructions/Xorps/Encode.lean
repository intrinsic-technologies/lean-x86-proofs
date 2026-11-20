import X86Proofs.Step.Address

/-!
# Encoding `xorps xmm, xmm`

The standard bytes of `xorps xmm, xmm` (`0F 57 /r`, register) for XMM registers given by number,
and that they name the registers.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/--
The bytes of `xorps dst, src` for XMM registers numbered `dst` and `src` (0–15), in the shortest
encoding: `0F 57` and ModRM with `mod = 3`, `reg = dst` and `rm = src` (low three bits), with no
prefix if both registers are 0–7, else after a REX prefix (W = 0) with REX.R and REX.B the top bits
of `dst` and `src`. E.g. `encodeXorpsXmmXmm 0 0 = [0x0F, 0x57, 0xC0]` (`xorps xmm0, xmm0`),
`encodeXorpsXmmXmm 9 1 = [0x44, 0x0F, 0x57, 0xC9]` (`xorps xmm9, xmm1`).
-/
def encodeXorpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if dst.toNat < 8 ∧ src.toNat < 8 then [0x0F, 0x57, modrm]
  else [UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, 0x57, modrm]

/-- `encodeXorpsXmmXmm` is a valid encoding of the registers it names. -/
theorem encodeXorpsXmmXmm_spec : ∀ dst src : BitVec 4,
    (∃ modrm, encodeXorpsXmmXmm dst src = [0x0F, 0x57, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeXorpsXmmXmm dst src = [rex, 0x0F, 0x57, modrm] ∧ RexPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : dst.toNat < 8 ∧ src.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert dst src
    decide

end X86Proofs
