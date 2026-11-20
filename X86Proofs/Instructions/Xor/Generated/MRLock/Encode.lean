import X86Proofs.Instructions.Xor.Generated.MR.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeXorLockM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeXorM64R64 src am

def encodeXorLockM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeXorM32R32 src am

def encodeXorLockM16R16 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeXorM16R16 src am

end X86Proofs
