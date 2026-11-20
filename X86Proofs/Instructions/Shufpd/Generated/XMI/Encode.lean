import X86Proofs.Instructions.Movups.Encode
import X86Proofs.Step.FetchImm

namespace X86Proofs

abbrev encodeShufpdXmmM128Imm8 (dst : BitVec 4) (am : AddrMode) (imm : BitVec 8) : List UInt8 :=
  0x66 :: (encodeSseMem 0xC6 dst am ++ immBytes 8 imm)

end X86Proofs
