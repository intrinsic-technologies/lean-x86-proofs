import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeNop1AM (pre : List UInt8) (reg : BitVec 3) (am : AddrMode) : List UInt8 :=
  pre ++ 0x0F :: 0x1A :: am.modrm reg :: am.tail

end X86Proofs
