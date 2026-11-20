import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePaddswMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xED dst am

end X86Proofs
