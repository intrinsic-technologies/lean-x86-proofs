import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsllqMmImm8 (dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  encodeMmxExtImm 0x73 6 dst imm

end X86Proofs
