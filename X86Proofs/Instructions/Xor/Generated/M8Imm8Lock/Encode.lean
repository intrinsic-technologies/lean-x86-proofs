import X86Proofs.Instructions.Xor.Generated.M8Imm8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeXorLockM8Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeXorM8Imm8 am imm

end X86Proofs
