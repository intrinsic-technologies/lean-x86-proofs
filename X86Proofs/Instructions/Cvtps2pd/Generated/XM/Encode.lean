import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeCvtps2pdXmmM64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMem 0x5A dst am

end X86Proofs
