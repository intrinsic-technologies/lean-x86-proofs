import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovmskpsR32Xmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x50 dst src

end X86Proofs
