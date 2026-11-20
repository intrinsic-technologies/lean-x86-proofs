import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeCvtsi2sdXmmM32 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF2 :: encodeSseMem 0x2A dst am

end X86Proofs
