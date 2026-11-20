import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtps2piMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x2D dst am

end X86Proofs
