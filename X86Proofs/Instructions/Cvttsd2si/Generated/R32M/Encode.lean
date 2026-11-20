import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeCvttsd2siR32M64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF2 :: encodeSseMem 0x2C dst am

end X86Proofs
