import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeNop1BM (pre : List UInt8) (reg : BitVec 3) (am : AddrMode) : List UInt8 :=
  pre ++ 0x0F :: 0x1B :: am.modrm reg :: am.tail

end X86Proofs
