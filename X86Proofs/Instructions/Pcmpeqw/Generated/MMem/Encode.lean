import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpeqwMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x75 dst am

end X86Proofs
