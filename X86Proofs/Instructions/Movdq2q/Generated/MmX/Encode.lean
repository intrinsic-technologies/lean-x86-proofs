import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovdq2qMmXmm (dst : BitVec 3) (src : BitVec 4) : List UInt8 :=
  0xF2 :: encodeMmxGpr 0xD6 dst src

end X86Proofs
