import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpgtwMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x65 dst am

end X86Proofs
