import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsllwMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xF1 dst am

end X86Proofs
