import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqMmM64 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMem 0x6F dst am

end X86Proofs
