import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePshufhwXmmXmmImm8 (dst src : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  0xF3 :: (encodeSseRegReg 0x70 dst src ++ immBytes 8 imm)

end X86Proofs
