import X86Proofs.Step.SseEncode
import X86Proofs.Step.FetchImm

namespace X86Proofs

abbrev encodePshufwMmM64Imm8 (dst : BitVec 3) (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  encodeMmxMem 0x70 dst am ++ immBytes 8 imm

end X86Proofs
