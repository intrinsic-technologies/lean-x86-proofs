import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodeCmpsdXmmXmmImm8 (dst src : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  0xF2 :: (encodeSseRegReg 0xC2 dst src ++ immBytes 8 imm)

end X86Proofs
