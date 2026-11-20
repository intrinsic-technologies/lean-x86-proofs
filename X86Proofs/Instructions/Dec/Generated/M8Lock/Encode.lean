import X86Proofs.Instructions.Dec.Generated.M8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeDecLockM8 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeDecM8 am

end X86Proofs
