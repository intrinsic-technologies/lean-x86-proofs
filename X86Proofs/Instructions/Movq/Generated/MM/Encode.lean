import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqMmMm (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x6F dst src

end X86Proofs
