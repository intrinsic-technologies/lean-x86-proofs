import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeCvtpi2psXmmM64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMem 0x2A dst am

end X86Proofs
