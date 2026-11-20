import X86Proofs.Instructions.Sub.Generated.MR.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeSubLockM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeSubM64R64 src am

def encodeSubLockM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeSubM32R32 src am

def encodeSubLockM16R16 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeSubM16R16 src am

end X86Proofs
