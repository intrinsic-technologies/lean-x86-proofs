import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePunpcklbwMmM32 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x60 dst am

end X86Proofs
