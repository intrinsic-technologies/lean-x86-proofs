import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsrlwXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xD1 dst src

end X86Proofs
