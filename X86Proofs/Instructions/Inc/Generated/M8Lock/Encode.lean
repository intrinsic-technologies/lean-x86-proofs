import X86Proofs.Instructions.Inc.Generated.M8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeIncLockM8 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeIncM8 am

end X86Proofs
