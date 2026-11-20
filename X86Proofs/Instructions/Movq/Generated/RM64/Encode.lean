import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqR64Mm (dst : BitVec 4) (src : BitVec 3) : List UInt8 :=
  encodeMmxGprW 0x7E src dst

end X86Proofs
