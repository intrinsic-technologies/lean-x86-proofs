import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsrawMmImm8 (dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  encodeMmxExtImm 0x71 4 dst imm

end X86Proofs
