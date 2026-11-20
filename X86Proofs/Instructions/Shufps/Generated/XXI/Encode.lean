import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeShufpsXmmXmmImm8 (dst src : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  (encodeSseRegReg 0xC6 dst src ++ immBytes 8 imm)

end X86Proofs
