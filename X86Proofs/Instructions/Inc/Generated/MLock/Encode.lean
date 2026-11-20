import X86Proofs.Instructions.Inc.Generated.M.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeIncLockM64 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeIncM64 am

def encodeIncLockM32 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeIncM32 am

def encodeIncLockM16 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeIncM16 am

end X86Proofs
