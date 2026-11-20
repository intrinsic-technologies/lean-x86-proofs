import X86Proofs.Step.Address

/-!
# Encoding `lea r64, [mem]`

The standard bytes of `lea r64, [mem]` (`REX.W 8D /r`) for a register given by number and any
`AddrMode`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The bytes of `lea dst, [am]` for the 64-bit register numbered `dst` (0–15): REX.W
(`am.rexByte true dst`: W, R from `dst`, X and B from `am`), `8D`, ModRM with `reg = dst & 7`, then
`am.tail`. E.g. `encodeLeaR64M 3 (.sib 4 none 0 (.d8 0x10)) = [0x48, 0x8D, 0x5C, 0x24, 0x10]`
(`lea rbx, [rsp + 0x10]`). -/
def encodeLeaR64M (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true dst :: 0x8D :: am.modrm (regLow dst) :: am.tail

end X86Proofs
