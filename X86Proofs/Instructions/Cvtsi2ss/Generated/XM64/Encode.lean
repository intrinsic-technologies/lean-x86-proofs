import X86Proofs.Instructions.Movups.Encode
import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCvtsi2ssXmmM64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF3 :: encodeSseMemW 0x2A dst am

end X86Proofs
