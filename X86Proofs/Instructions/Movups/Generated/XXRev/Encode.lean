import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovupsXmmXmmRev (dst src : BitVec 4) : List UInt8 :=
  encodeSseRegReg 0x11 src dst

end X86Proofs
