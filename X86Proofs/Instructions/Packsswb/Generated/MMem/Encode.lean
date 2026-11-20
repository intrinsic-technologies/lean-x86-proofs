import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePacksswbMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x63 dst am

end X86Proofs
