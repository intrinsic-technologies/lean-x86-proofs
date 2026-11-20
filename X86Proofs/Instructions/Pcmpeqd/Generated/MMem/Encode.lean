import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpeqdMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x76 dst am

end X86Proofs
