import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsubwMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xF9 dst am

end X86Proofs
