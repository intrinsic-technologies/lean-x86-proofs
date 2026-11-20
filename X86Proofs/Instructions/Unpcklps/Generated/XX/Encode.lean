import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeUnpcklpsXmmXmm (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x14 dst src

end X86Proofs
