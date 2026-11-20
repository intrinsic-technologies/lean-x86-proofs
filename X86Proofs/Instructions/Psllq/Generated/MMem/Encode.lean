import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsllqMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xF3 dst am

end X86Proofs
