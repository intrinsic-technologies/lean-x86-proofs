import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeCvtsd2ssXmmM64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF2 :: encodeSseMem 0x5A dst am

end X86Proofs
