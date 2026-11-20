import X86Proofs.Instructions.Sub.Generated.M8R8.Encode

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def encodeSubLockM8R8 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeSubM8R8 src am

def encodeSubLockM8R8NoRex (src : BitVec 3) (am : AddrMode) : List UInt8 :=
  0xF0 :: encodeSubM8R8NoRex src am

end X86Proofs
