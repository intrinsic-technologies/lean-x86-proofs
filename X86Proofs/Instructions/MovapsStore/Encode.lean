import X86Proofs.Step.Address

/-!
# Encoding `movaps [mem], xmm`

The standard bytes of `movaps [mem], xmm` (`0F 29 /r`) for an XMM register given by number and
any `AddrMode`, in the shortest encoding.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/--
The bytes of `movaps [am], src` for the XMM register numbered `src` (0–15), in the shortest
encoding: `0F 29`, ModRM with `reg = src & 7`, `am.tail`; without a prefix if neither `src` nor
`am` needs a REX bit, else after `am.rexByte false src`. E.g.
`encodeMovapsM128Xmm 0 (.sib 4 none 0 (.d8 0x10)) = [0x0F, 0x29, 0x44, 0x24, 0x10]`
(`movaps [rsp + 0x10], xmm0`).
-/
def encodeMovapsM128Xmm (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex src then 0x0F :: 0x29 :: am.modrm (regLow src) :: am.tail
  else am.rexByte false src :: 0x0F :: 0x29 :: am.modrm (regLow src) :: am.tail

end X86Proofs
