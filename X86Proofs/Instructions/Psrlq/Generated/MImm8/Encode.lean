import X86Proofs.Step.SseEncode

namespace X86Proofs

abbrev encodePsrlqMmImm8 (dst : BitVec 3) (imm : BitVec 8) : List UInt8 :=
  encodeMmxExtImm 0x73 2 dst imm

end X86Proofs
