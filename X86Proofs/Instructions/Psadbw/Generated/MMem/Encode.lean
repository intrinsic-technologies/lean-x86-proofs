import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsadbwMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0xF6 dst am

end X86Proofs
