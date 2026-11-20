import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePadduswMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xDD dst am

end X86Proofs
