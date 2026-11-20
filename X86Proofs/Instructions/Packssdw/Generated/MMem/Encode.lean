import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePackssdwMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x6B dst am

end X86Proofs
