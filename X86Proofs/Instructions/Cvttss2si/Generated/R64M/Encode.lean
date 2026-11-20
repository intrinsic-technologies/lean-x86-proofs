import X86Proofs.Instructions.Movups.Encode
import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvttss2siR64M32 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF3 :: encodeSseMemW 0x2C dst am

end X86Proofs
