import X86Proofs.Instructions.Neg.Generated.M8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeNegLockM8 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeNegM8 am

end X86Proofs
