import X86Proofs.Instructions.Movups.Encode
import X86Proofs.Step.FetchImm

namespace X86Proofs

abbrev encodePshuflwXmmM128Imm8 (dst : BitVec 4) (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0xF2 :: (encodeSseMem 0x70 dst am ++ immBytes 8 imm)

end X86Proofs
