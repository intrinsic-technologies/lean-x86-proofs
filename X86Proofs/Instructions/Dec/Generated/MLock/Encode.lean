import X86Proofs.Instructions.Dec.Generated.M.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeDecLockM64 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeDecM64 am

def encodeDecLockM32 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeDecM32 am

def encodeDecLockM16 (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeDecM16 am

end X86Proofs
