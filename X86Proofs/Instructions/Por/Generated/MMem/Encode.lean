import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePorMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xEB dst am

end X86Proofs
