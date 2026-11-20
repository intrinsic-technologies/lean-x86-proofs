import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePcmpgtwXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0x65 dst src

end X86Proofs
