import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsrlqXmmXmm (dst src : BitVec 4) : List UInt8 :=
  0x66 :: encodeSseRegReg 0xD3 dst src

end X86Proofs
