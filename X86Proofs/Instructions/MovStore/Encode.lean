import X86Proofs.Step.Address

/-!
# Encoding stores

The standard bytes of `mov qword [mem], r64` (`REX.W 89 /r`) and `mov qword [mem], imm32`
(`REX.W C7 /0`) for a register given by number and any `AddrMode`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The bytes of `mov qword [am], src` for the 64-bit register numbered `src` (0–15): REX.W
(`am.rexByte true src`: R from `src`, X and B from `am`), `89`, ModRM with `reg = src & 7`, `am.tail`.
E.g. `encodeMovM64R64 1 (.sib 4 none 0 (.d8 0xC8)) = [0x48, 0x89, 0x4C, 0x24, 0xC8]`
(`mov [rsp - 0x38], rcx`). -/
def encodeMovM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true src :: 0x89 :: am.modrm (regLow src) :: am.tail

/-- The bytes of `mov qword [am], imm32`: REX.W (X and B from `am`), `C7`, ModRM with `reg = 0`,
`am.tail`, the immediate (little-endian). -/
def encodeMovM64Imm32 (am : AddrMode) (imm : BitVec 32) : List UInt8 :=
  am.rexByte true 0 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)

end X86Proofs
