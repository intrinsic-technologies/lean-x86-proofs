import X86Proofs.Instructions.Movups.Encode

/-!
# Encoding `xorps xmm, [mem]`

The standard bytes of `xorps xmm, [mem]` (`0F 57 /r`): `encodeSseMem 0x57`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The bytes of `xorps dst, [am]` (`encodeSseMem 0x57`). E.g.
`encodeXorpsXmmM128 0 (.sib 4 none 0 (.d8 0x10)) = [0x0F, 0x57, 0x44, 0x24, 0x10]`
(`xorps xmm0, [rsp + 0x10]`). -/
abbrev encodeXorpsXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 := encodeSseMem 0x57 dst am

end X86Proofs
