import X86Proofs.Instructions.Movups.Encode
import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeMovntiM64R64 (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  encodeSseMemW 0xC3 src am

end X86Proofs
