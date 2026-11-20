import X86Proofs.Instructions.Cmpxchg8b.Generated.M64.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeCmpxchg8bLockM64 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeCmpxchg8bM64 am

end X86Proofs
