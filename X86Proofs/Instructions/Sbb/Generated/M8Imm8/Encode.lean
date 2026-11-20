import X86Proofs.Step.Address

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeSbbM8Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0x80 :: am.modrm 3 :: (am.tail ++ [UInt8.ofBitVec imm])

end X86Proofs
