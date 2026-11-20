import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtpd2piMmM128 (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeMmxMem 0x2D dst am

end X86Proofs
