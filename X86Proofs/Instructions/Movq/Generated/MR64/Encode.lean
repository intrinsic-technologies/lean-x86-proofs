import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqMmR64 (dst : BitVec 3) (src : BitVec 4) : List UInt8 :=
  encodeMmxGprW 0x6E dst src

end X86Proofs
