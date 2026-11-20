import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePunpckhdqMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x6A dst am

end X86Proofs
