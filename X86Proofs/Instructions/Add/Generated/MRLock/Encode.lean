import X86Proofs.Instructions.Add.Generated.MR.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeAddLockM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeAddM64R64 src am

def encodeAddLockM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeAddM32R32 src am

def encodeAddLockM16R16 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeAddM16R16 src am

end X86Proofs
