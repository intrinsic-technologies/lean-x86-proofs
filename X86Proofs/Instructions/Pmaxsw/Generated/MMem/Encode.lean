import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePmaxswMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xEE dst am

end X86Proofs
