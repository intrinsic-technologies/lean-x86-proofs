import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovntiM32R32 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMem 0xC3 src am

end X86Proofs
