import X86Proofs.Instructions.Xadd.Generated.MR.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeXaddLockM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeXaddM64R64 src am

def encodeXaddLockM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeXaddM32R32 src am

def encodeXaddLockM16R16 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeXaddM16R16 src am

end X86Proofs
