import X86Proofs.Instructions.Add.Generated.M8Imm8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeAddLockM8Imm8 (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF0 :: encodeAddM8Imm8 am imm

end X86Proofs
