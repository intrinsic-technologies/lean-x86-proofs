import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeCvtdq2pdXmmM64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF3 :: encodeSseMem 0xE6 dst am

end X86Proofs
