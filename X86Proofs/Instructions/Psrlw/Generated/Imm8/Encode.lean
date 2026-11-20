import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsrlwXmmImm8 (dst : BitVec 4) (imm : BitVec 8) : List UInt8 :=
  0x66 :: encodeSseExtImm 0x71 2 dst imm

end X86Proofs
