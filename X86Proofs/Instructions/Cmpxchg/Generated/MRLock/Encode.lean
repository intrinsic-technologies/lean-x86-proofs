import X86Proofs.Instructions.Cmpxchg.Generated.MR.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeCmpxchgLockM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeCmpxchgM64R64 src am

def encodeCmpxchgLockM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeCmpxchgM32R32 src am

def encodeCmpxchgLockM16R16 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeCmpxchgM16R16 src am

end X86Proofs
