import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovdMmR32 (dst : BitVec 3) (src : BitVec 4) : List UInt8 :=
  encodeMmxGpr 0x6E dst src

end X86Proofs
