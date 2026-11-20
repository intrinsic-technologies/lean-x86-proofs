import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqM64Mm7e (src : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMemW 0x7E src am

end X86Proofs
