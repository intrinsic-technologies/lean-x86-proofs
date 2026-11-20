import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqMmMmRev (dst src : BitVec 3) : List UInt8 :=
  encodeMmxRegReg 0x7F src dst

end X86Proofs
