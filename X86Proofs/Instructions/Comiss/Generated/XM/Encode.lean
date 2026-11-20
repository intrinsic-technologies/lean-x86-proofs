import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeComissXmmM32 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMem 0x2F dst am

end X86Proofs
