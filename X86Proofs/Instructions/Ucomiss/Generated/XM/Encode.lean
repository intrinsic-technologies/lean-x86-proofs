import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeUcomissXmmM32 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMem 0x2E dst am

end X86Proofs
