import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePunpcklwdMmM32 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x61 dst am

end X86Proofs
