import X86Proofs.Instructions.Not.Generated.M8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeNotLockM8 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeNotM8 am

end X86Proofs
