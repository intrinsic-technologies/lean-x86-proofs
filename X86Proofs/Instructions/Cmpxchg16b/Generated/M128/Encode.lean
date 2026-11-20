import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeCmpxchg16bM128 (am : AddrMode) : List UInt8 :=
  am.rexByte true 0 :: 0x0F :: 0xC7 :: am.modrm 1 :: am.tail

end X86Proofs
