import X86Proofs.Step.Address

/-!
# Encoding legacy SSE register-register instructions

The standard bytes of a legacy SSE instruction `0F op /r` on two XMM registers given by number
(`encodeSseRegReg op dst src`, before any mandatory prefix such as `66`), in the shortest
encoding, and that they name the registers (`encodeSseRegReg_spec`). The memory-operand
counterpart is `encodeSseMem` (`Instructions/Movups/Encode.lean`). A group opcode with an
immediate on one XMM register, `0F op /ext ib` (the shifts by an immediate, `0F 71`–`73`), is
`encodeSseExtImm op ext dst imm` (`encodeSseExtImm_spec`). For the forms between an XMM and a
general-purpose register that fix REX.W, `encodeSseRegReg_spec_noW` (W = 0, `MOVD`) and
`encodeSseRegRegW` (W = 1, `MOVQ`), and with a memory operand `encodeSseMemW` (W = 1, `MOVQ xmm,
m64`).

The MMX forms (`NP 0F op /r` on MMX registers 0–7, which take no REX bit): `encodeMmxRegReg op dst
src` (`encodeMmxRegReg_spec`) and, with a memory operand, `encodeMmxMem op dst am`
(`encodeMmxMem_spec`: a REX prefix only for the address's X and B bits); a group opcode with an
immediate, `0F op /ext ib` (the MMX shifts by an immediate), is `encodeMmxExtImm op ext dst imm`
(`encodeMmxExtImm_spec`). The MMX forms with a REX.W prefix: `encodeMmxMemW op dst am` (`MOVQ mm,
m64`, `REX.W 0F 6E`); with a general-purpose register in ModRM `rm`: `encodeMmxGpr op dst src`
(REX only for registers 8–15, W = 0; `MOVD mm, r32`) and `encodeMmxGprW op dst src` (W = 1;
`MOVQ mm, r64`); with the general-purpose register in ModRM `reg` and the MMX register in `rm`:
`encodeGprMmx op dst src` (REX.R for registers 8–15; `PMOVMSKB r32, mm`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The bytes of `0F op /r` with XMM registers `dst` (ModRM `reg`) and `src` (ModRM `rm`), 0–15:
`0F op` and ModRM with `mod = 3` and the registers' low three bits, after a REX prefix (W = 0)
carrying their top bits (REX.R, REX.B) if either is 8–15. E.g. `encodeSseRegReg 0xFC 1 2 =
[0x0F, 0xFC, 0xCA]`, `encodeSseRegReg 0xFC 9 2 = [0x44, 0x0F, 0xFC, 0xCA]`. -/
def encodeSseRegReg (op : UInt8) (dst src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)
  if dst.toNat < 8 ∧ src.toNat < 8 then [0x0F, op, modrm]
  else [UInt8.ofNat (0x40 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, op, modrm]

/-- `encodeSseRegReg` is a valid encoding of the registers it names: without REX, registers 0–7
from ModRM; with a REX prefix, extended by REX.R and REX.B. -/
theorem encodeSseRegReg_spec (op : UInt8) : ∀ dst src : BitVec 4,
    (∃ modrm, encodeSseRegReg op dst src = [0x0F, op, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeSseRegReg op dst src = [rex, 0x0F, op, modrm] ∧
      RexPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
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

/-- The bytes of `0F op /ext ib` on XMM register `dst` (ModRM `rm`), 0–15, with the opcode
extension `ext` in ModRM `reg` and the immediate `imm` after ModRM: `0F op`, ModRM with `mod = 3`,
the immediate, after a REX prefix (`41`, REX.B) if `dst` is 8–15. -/
def encodeSseExtImm (op : UInt8) (ext : BitVec 3) (dst : BitVec 4) (imm : BitVec 8) :
    List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * ext.toNat + dst.toNat % 8)
  if dst.toNat < 8 then 0x0F :: op :: modrm :: immBytes 8 imm
  else 0x41 :: 0x0F :: op :: modrm :: immBytes 8 imm

/-- `encodeSseExtImm` is a valid encoding of the register it names, with the extension in ModRM
`reg`: without REX, registers 0–7 from ModRM; with a REX prefix, extended by REX.B. -/
theorem encodeSseExtImm_spec (op : UInt8) (imm : BitVec 8) : ∀ (ext : BitVec 3) (dst : BitVec 4),
    (∃ modrm, encodeSseExtImm op ext dst imm = 0x0F :: op :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = ext ∧
      gprNumber 0 0 (modrmRm modrm) = dst.setWidth 5) ∨
    (∃ rex modrm, encodeSseExtImm op ext dst imm = rex :: 0x0F :: op :: modrm :: immBytes 8 imm ∧
      RexPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = ext ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = dst.setWidth 5) := by
  intro ext dst
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert ext dst
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexPrefix
    revert ext dst
    decide

/-- `encodeSseRegReg`'s REX prefix, when there is one, has W = 0 (`40`–`47`): the encoding of the
forms that require REX.W clear (`MOVD xmm, r32`, `66 0F 6E`). -/
theorem encodeSseRegReg_spec_noW (op : UInt8) : ∀ dst src : BitVec 4,
    (∃ modrm, encodeSseRegReg op dst src = [0x0F, op, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeSseRegReg op dst src = [rex, 0x0F, op, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : dst.toNat < 8 ∧ src.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

/-- The bytes of `REX.W 0F op /r` with registers `dst` (ModRM `reg`) and `src` (ModRM `rm`), 0–15:
a REX prefix with W = 1 carrying the registers' top bits, `0F op`, and ModRM with `mod = 3` (the
forms that require REX.W, `MOVQ xmm, r64`, `66 REX.W 0F 6E`). -/
def encodeSseRegRegW (op : UInt8) (dst src : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + 4 * (dst.toNat / 8) + src.toNat / 8), 0x0F, op,
    UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat % 8)]

/-- `encodeSseRegRegW` is a valid encoding of the registers it names, extended by REX.R and
REX.B. -/
theorem encodeSseRegRegW_spec (op : UInt8) : ∀ dst src : BitVec 4,
    ∃ rex modrm, encodeSseRegRegW op dst src = [rex, 0x0F, op, modrm] ∧
      RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

/-- The bytes of `REX.W 0F op /r` with XMM register `dst` (0–15) in ModRM `reg` and a memory
operand `am`: a REX prefix with W = 1 carrying `dst`'s top bit and the bits `am` needs
(`am.rexByte true dst`, `AddrMode.rexByte_true_spec`), `0F op`, ModRM and the address bytes (the
memory forms that require REX.W, `MOVQ xmm, m64`, `66 REX.W 0F 6E`). -/
def encodeSseMemW (op : UInt8) (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true dst :: 0x0F :: op :: am.modrm (regLow dst) :: am.tail

/-- The bytes of `0F op /r` with MMX registers `dst` (ModRM `reg`) and `src` (ModRM `rm`), 0–7:
`0F op` and ModRM with `mod = 3`. E.g. `encodeMmxRegReg 0xFC 1 2 = [0x0F, 0xFC, 0xCA]`
(`paddb mm1, mm2`). -/
def encodeMmxRegReg (op : UInt8) (dst src : BitVec 3) : List UInt8 :=
  [0x0F, op, UInt8.ofNat (0xC0 + 8 * dst.toNat + src.toNat)]

/-- `encodeMmxRegReg` names its registers in ModRM. -/
theorem encodeMmxRegReg_spec (op : UInt8) (dst src : BitVec 3) :
    ∃ modrm, encodeMmxRegReg op dst src = [0x0F, op, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = dst ∧ modrmRm modrm = src :=
  ⟨_, rfl, by revert dst src; decide⟩

/-- The bytes of `0F op /ext ib` on MMX register `dst` (ModRM `rm`, 0–7) with the opcode extension
`ext` in ModRM `reg` and the immediate `imm` after ModRM. -/
def encodeMmxExtImm (op : UInt8) (ext dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  0x0F :: op :: UInt8.ofNat (0xC0 + 8 * ext.toNat + dst.toNat) :: immBytes 8 imm

/-- `encodeMmxExtImm` names its register and extension in ModRM. -/
theorem encodeMmxExtImm_spec (op : UInt8) (ext dst : BitVec 3) (imm : BitVec 8) :
    ∃ modrm, encodeMmxExtImm op ext dst imm = 0x0F :: op :: modrm :: immBytes 8 imm ∧
      modrmMod modrm = 3 ∧ modrmReg modrm = ext ∧ modrmRm modrm = dst :=
  ⟨_, rfl, by revert ext dst; decide⟩

/-- The bytes of `0F op /r` with MMX register `dst` (0–7) in ModRM `reg` and a memory operand `am`:
`0F op`, ModRM and the address bytes, after a REX prefix (W = 0, R = 0) if `am` needs its X or B
bit. -/
def encodeMmxMem (op : UInt8) (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  if am.rexX = 0 ∧ am.rexB = 0 then 0x0F :: op :: am.modrm dst :: am.tail
  else am.rexByte false 0 :: 0x0F :: op :: am.modrm dst :: am.tail

/-- `encodeMmxMem` is a valid encoding of the register and address it names. -/
theorem encodeMmxMem_spec (op : UInt8) (dst : BitVec 3) (am : AddrMode) :
    (encodeMmxMem op dst am = 0x0F :: op :: am.modrm dst :: am.tail ∧ am.rexX = 0 ∧
      am.rexB = 0) ∨
    (encodeMmxMem op dst am = am.rexByte false 0 :: 0x0F :: op :: am.modrm dst :: am.tail ∧
      RexNoWPrefix (am.rexByte false 0).toBitVec ∧ rexX (am.rexByte false 0).toBitVec = am.rexX ∧
      rexB (am.rexByte false 0).toBitVec = am.rexB) := by
  unfold encodeMmxMem
  by_cases hc : am.rexX = 0 ∧ am.rexB = 0
  · exact .inl ⟨ite_eq_left hc, hc.1, hc.2⟩
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    exact .inr ⟨ite_eq_right hc, hrex, hx, hb⟩

/-- The bytes of `REX.W 0F op /r` with MMX register `dst` in ModRM `reg` and a memory operand `am`:
a REX prefix with W = 1 and the X and B bits `am` needs, `0F op`, ModRM and the address bytes. -/
def encodeMmxMemW (op : UInt8) (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  am.rexByte true 0 :: 0x0F :: op :: am.modrm dst :: am.tail

/-- `encodeMmxMemW` is a valid encoding of the register and address it names, with REX.W. -/
theorem encodeMmxMemW_spec (op : UInt8) (dst : BitVec 3) (am : AddrMode) :
    encodeMmxMemW op dst am = am.rexByte true 0 :: 0x0F :: op :: am.modrm dst :: am.tail ∧
      RexWPrefix (am.rexByte true 0).toBitVec ∧ rexX (am.rexByte true 0).toBitVec = am.rexX ∧
      rexB (am.rexByte true 0).toBitVec = am.rexB := by
  obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_true_spec 0
  exact ⟨rfl, hrex, hx, hb⟩

/-- The bytes of `0F op /r` with MMX register `dst` (ModRM `reg`, 0–7) and general-purpose
register `src` (ModRM `rm`, 0–15): after a REX prefix (`41`, REX.B) if `src` is 8–15. -/
def encodeMmxGpr (op : UInt8) (dst : BitVec 3) (src : BitVec 4) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * dst.toNat + src.toNat % 8)
  if src.toNat < 8 then [0x0F, op, modrm] else [0x41, 0x0F, op, modrm]

/-- `encodeMmxGpr` names its registers: without REX, `src` 0–7 from ModRM; with a REX prefix (W =
0), extended by REX.B. -/
theorem encodeMmxGpr_spec (op : UInt8) : ∀ (dst : BitVec 3) (src : BitVec 4),
    (∃ modrm, encodeMmxGpr op dst src = [0x0F, op, modrm] ∧ modrmMod modrm = 3 ∧
      modrmReg modrm = dst ∧ gprNumber 0 0 (modrmRm modrm) = src.setWidth 5) ∨
    (∃ rex modrm, encodeMmxGpr op dst src = [rex, 0x0F, op, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = dst ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5) := by
  intro dst src
  by_cases hlow : src.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

/-- The bytes of `REX.W 0F op /r` with MMX register `dst` (ModRM `reg`) and general-purpose
register `src` (ModRM `rm`, 0–15, its top bit in REX.B). -/
def encodeMmxGprW (op : UInt8) (dst : BitVec 3) (src : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48 + src.toNat / 8), 0x0F, op,
    UInt8.ofNat (0xC0 + 8 * dst.toNat + src.toNat % 8)]

/-- `encodeMmxGprW` names its registers, `src` extended by REX.B. -/
theorem encodeMmxGprW_spec (op : UInt8) : ∀ (dst : BitVec 3) (src : BitVec 4),
    ∃ rex modrm, encodeMmxGprW op dst src = [rex, 0x0F, op, modrm] ∧
      RexWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧ modrmReg modrm = dst ∧
      gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm) = src.setWidth 5 := by
  intro dst src
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst src
  decide

/-- The bytes of `0F op /r` with general-purpose register `dst` (ModRM `reg`, 0–15) and MMX register
`src` (ModRM `rm`, 0–7): after a REX prefix (`44`, REX.R) if `dst` is 8–15. -/
def encodeGprMmx (op : UInt8) (dst : BitVec 4) (src : BitVec 3) : List UInt8 :=
  let modrm := UInt8.ofNat (0xC0 + 8 * (dst.toNat % 8) + src.toNat)
  if dst.toNat < 8 then [0x0F, op, modrm] else [0x44, 0x0F, op, modrm]

/-- `encodeGprMmx` names its registers: `dst` from ModRM `reg`, extended by REX.R. -/
theorem encodeGprMmx_spec (op : UInt8) : ∀ (dst : BitVec 4) (src : BitVec 3),
    (∃ modrm, encodeGprMmx op dst src = [0x0F, op, modrm] ∧ modrmMod modrm = 3 ∧
      gprNumber 0 0 (modrmReg modrm) = dst.setWidth 5 ∧ modrmRm modrm = src) ∨
    (∃ rex modrm, encodeGprMmx op dst src = [rex, 0x0F, op, modrm] ∧
      RexNoWPrefix rex.toBitVec ∧ modrmMod modrm = 3 ∧
      gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = dst.setWidth 5 ∧ modrmRm modrm = src) := by
  intro dst src
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst src
    decide
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst src
    decide

end X86Proofs
