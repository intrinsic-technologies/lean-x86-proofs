import X86Proofs.Instructions.Btr.Generated.MR.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeBtrLockM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeBtrM64R64 src am

def encodeBtrLockM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeBtrM32R32 src am

def encodeBtrLockM16R16 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeBtrM16R16 src am

end X86Proofs
