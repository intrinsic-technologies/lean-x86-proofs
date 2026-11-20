import X86Proofs.Instructions.Not.Generated.M.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeNotLockM64 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeNotM64 am

def encodeNotLockM32 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeNotM32 am

def encodeNotLockM16 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeNotM16 am

end X86Proofs
