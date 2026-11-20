import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePaddwMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xFD dst am

end X86Proofs
