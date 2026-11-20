import X86Proofs.Step.Address
import X86Proofs.Instructions.Mov.Decode

/-!
# Encoding MOV with register operands

The standard bytes of `mov r, r` (`89 /r`), `mov r, imm` (`B8+r`) and `mov r64, imm32` (`C7 /0`)
for registers given by number, and that they are encodings of what they name (`_spec`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/--
The bytes of `mov dst, src` for 64-bit registers numbered `dst` and `src` (0–15): REX.W with
REX.R and REX.B the top bits of `src` and `dst`, opcode `89`, and ModRM with `mod = 3`,
`reg = src` and `rm = dst` (low three bits). E.g. `encodeMovR64R64 0 3 = [0x48, 0x89, 0xD8]`,
`mov rax, rbx`.
-/
def encodeMovR64R64 (dst src : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + 4 * (src.toNat / 8) + dst.toNat / 8), 0x89,
    UInt8.ofNat (0xC0 + 8 * (src.toNat % 8) + dst.toNat % 8)]

/-- `encodeMovR64R64` is a valid encoding of the registers it names. -/
theorem encodeMovR64R64_spec : ∀ dst src : BitVec 4, ∃ rex modrm,
    encodeMovR64R64 dst src = [rex, 0x89, modrm] ∧ RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 ∧
    gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

/--
The bytes of `mov dst, src` for 32-bit registers numbered `dst` and `src` (0–15), in the
shortest encoding: opcode `89` and ModRM with `mod = 3`, `reg = src` and `rm = dst` (low three
bits), with no prefix if both registers are 0–7, else after a REX prefix with W = 0 and REX.R and
REX.B the top bits of `src` and `dst`. E.g. `encodeMovR32R32 0 3 = [0x89, 0xD8]` (`mov eax, ebx`).
-/
def encodeMovR32R32 (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (src.toNat % 8) + dst.toNat % 8)
  if src.toNat < 8 ∧ dst.toNat < 8 then [0x89, modrm]
  else [UInt8.ofNat (0x40 + 4 * (src.toNat / 8) + dst.toNat / 8), 0x89, modrm]

/-- `encodeMovR32R32` is a valid encoding of the registers it names: without a prefix, or with a
REX prefix with W = 0. -/
theorem encodeMovR32R32_spec : ∀ dst src : BitVec 4,
    (∃ modrm, encodeMovR32R32 dst src = [0x89, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmReg modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeMovR32R32 dst src = [rex, 0x89, modrm] ∧ RexNoWPrefix rex.toBitVec ∧
      modrmMod modrm = 3 ∧ gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : src.toNat < 8 ∧ dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

/--
The bytes of `mov dst, imm` for the 32-bit register numbered `dst` (0–15), in the shortest
encoding: opcode `B8 + (dst & 7)` and the four bytes of `imm`, after a REX prefix `41` (REX.B) if
`dst` is 8–15. E.g. `encodeMovR32Imm32 0 1 = [0xB8, 1, 0, 0, 0]` (`mov eax, 1`),
`encodeMovR32Imm32 14 imm = [0x41, 0xBE, …]` (`mov r14d, imm`).
-/
def encodeMovR32Imm32 (dst : BitVec 4) (imm : BitVec 32) : List UInt8 :=
  if dst.toNat < 8 then UInt8.ofNat (0xB8 + dst.toNat) :: immBytes 32 imm
  else 0x41 :: UInt8.ofNat (0xB8 + dst.toNat % 8) :: immBytes 32 imm

/-- `encodeMovR32Imm32` is a valid encoding of the register and immediate it names. -/
theorem encodeMovR32Imm32_spec (dst : BitVec 4) (imm : BitVec 32) :
    (∃ op, encodeMovR32Imm32 dst imm = op :: immBytes 32 imm ∧ MovImmOpcode op ∧
      gprNumber 0 0 (opcodeReg op) = dst.setWidth 5) ∨
    (∃ rex op, encodeMovR32Imm32 dst imm = rex :: op :: immBytes 32 imm ∧ RexNoWPrefix rex.toBitVec ∧
      MovImmOpcode op ∧ gprNumber 0 (rexB rex.toBitVec) (opcodeReg op) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide

/--
The bytes of `mov dst, imm` for the 64-bit register numbered `dst` (0–15) and a 64-bit
immediate: REX.W with REX.B the top bit of `dst`, opcode `B8 + (dst & 7)` and the eight bytes of
`imm` (`movabs`).
-/
def encodeMovR64Imm64 (dst : BitVec 4) (imm : BitVec 64) : List UInt8 :=
  UInt8.ofNat (0x48 + dst.toNat / 8) :: UInt8.ofNat (0xB8 + dst.toNat % 8) :: immBytes 64 imm

theorem encodeMovR64Imm64_spec (dst : BitVec 4) (imm : BitVec 64) : ∃ rex op,
    encodeMovR64Imm64 dst imm = rex :: op :: immBytes 64 imm ∧ RexWPrefix rex.toBitVec ∧
    MovImmOpcode op ∧ gprNumber 0 (rexB rex.toBitVec) (opcodeReg op) = dst.setWidth 5 := by
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

/--
The bytes of `mov dst, imm` for the 64-bit register numbered `dst` (0–15) and a 32-bit
immediate, sign-extended: REX.W with REX.B the top bit of `dst`, opcode `C7`, ModRM with
`mod = 3`, `reg = 0` and `rm = dst` (low three bits), and the four bytes of `imm`. E.g.
`encodeMovR64Imm32 0 1 = [0x48, 0xC7, 0xC0, 1, 0, 0, 0]` (`mov rax, 1`).
-/
def encodeMovR64Imm32 (dst : BitVec 4) (imm : BitVec 32) : List UInt8 :=
  UInt8.ofNat (0x48 + dst.toNat / 8) :: 0xC7 :: UInt8.ofNat (0xC0 + dst.toNat % 8) ::
    immBytes 32 imm

theorem encodeMovR64Imm32_spec (dst : BitVec 4) (imm : BitVec 32) : ∃ rex modrm,
    encodeMovR64Imm32 dst imm = rex :: 0xC7 :: modrm :: immBytes 32 imm ∧ RexWPrefix rex.toBitVec ∧
    modrmMod modrm = 3 ∧ modrmReg modrm = 0 ∧
    gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5 := by
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide

end X86Proofs
