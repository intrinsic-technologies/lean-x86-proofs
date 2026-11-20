import X86Proofs.Instructions.Movups.Encode
import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqXmmM64Rexw (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMemW 0x6E dst am

end X86Proofs
