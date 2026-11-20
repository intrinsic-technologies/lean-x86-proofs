import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePminubMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xDA dst am

end X86Proofs
