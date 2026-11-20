import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeUnpckhpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x15 dst src

end X86Proofs
