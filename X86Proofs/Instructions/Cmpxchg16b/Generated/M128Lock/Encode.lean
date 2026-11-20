import X86Proofs.Instructions.Cmpxchg16b.Generated.M128.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeCmpxchg16bLockM128 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeCmpxchg16bM128 am

end X86Proofs
