import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqMmM646e (dst : BitVec 3) (am : AddrMode) : List UInt8 :=
  encodeMmxMemW 0x6E dst am

end X86Proofs
