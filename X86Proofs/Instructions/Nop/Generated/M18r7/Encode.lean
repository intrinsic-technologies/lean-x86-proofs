import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeNop18R7M (pre : List UInt8) (am : AddrMode) : List UInt8 :=
  pre ++ 0x0F :: 0x18 :: am.modrm 7 :: am.tail

end X86Proofs
