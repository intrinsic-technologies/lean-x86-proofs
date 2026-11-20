import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovdR32Mm (dst : BitVec 4) (src : BitVec 3) : List UInt8 :=
  encodeMmxGpr 0x7E src dst

end X86Proofs
