import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeSubM8Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0x80 :: am.modrm 5 :: (am.tail ++ [UInt8.ofBitVec imm])

end X86Proofs
