import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeCvttss2siR32M32 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF3 :: encodeSseMem 0x2C dst am

end X86Proofs
