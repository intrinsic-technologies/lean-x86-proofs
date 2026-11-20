import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePunpckhwdMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x69 dst am

end X86Proofs
