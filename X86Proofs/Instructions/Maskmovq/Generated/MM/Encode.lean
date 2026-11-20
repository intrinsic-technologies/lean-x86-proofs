import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMaskmovqMmMm (src mask : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0xF7 src mask

end X86Proofs
