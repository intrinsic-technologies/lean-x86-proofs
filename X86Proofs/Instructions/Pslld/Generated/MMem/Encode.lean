import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePslldMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xF2 dst am

end X86Proofs
