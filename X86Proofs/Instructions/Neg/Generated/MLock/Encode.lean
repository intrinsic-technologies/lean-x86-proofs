import X86Proofs.Instructions.Neg.Generated.M.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeNegLockM64 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeNegM64 am

def encodeNegLockM32 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeNegM32 am

def encodeNegLockM16 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeNegM16 am

end X86Proofs
