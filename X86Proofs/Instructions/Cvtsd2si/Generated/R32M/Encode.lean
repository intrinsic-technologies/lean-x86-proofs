import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeCvtsd2siR32M64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF2 :: encodeSseMem 0x2D dst am

end X86Proofs
