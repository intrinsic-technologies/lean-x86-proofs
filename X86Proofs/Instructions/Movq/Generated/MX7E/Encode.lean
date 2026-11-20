import X86Proofs.Instructions.Movups.Encode
import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovqM64XmmRexw (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0x66 :: encodeSseMemW 0x7E src am

end X86Proofs
