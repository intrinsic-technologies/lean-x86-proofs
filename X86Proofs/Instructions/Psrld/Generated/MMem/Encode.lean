import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsrldMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xD2 dst am

end X86Proofs
