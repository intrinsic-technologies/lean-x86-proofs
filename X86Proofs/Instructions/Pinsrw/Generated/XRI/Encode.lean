import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePinsrwXmmR32Imm8 (dst src : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  0x66 :: (encodeSseRegReg 0xC4 dst src ++ immBytes 8 imm)

end X86Proofs
