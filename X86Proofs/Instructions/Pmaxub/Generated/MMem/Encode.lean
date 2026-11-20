import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmaxubMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xDE dst am

end X86Proofs
