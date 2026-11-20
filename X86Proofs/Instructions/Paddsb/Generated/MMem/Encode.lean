import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePaddsbMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xEC dst am

end X86Proofs
