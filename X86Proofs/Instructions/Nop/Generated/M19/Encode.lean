import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeNop19M (pre : List UInt8) (reg : BitVec 3) (am : AddrMode) : List UInt8 :=
  pre ++ 0x0F :: 0x19 :: am.modrm reg :: am.tail

end X86Proofs
