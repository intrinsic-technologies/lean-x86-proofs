import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeMovssM32Xmm (src : BitVec 4) (am : AddrMode) : List UInt8 :=
  0xF3 :: encodeSseMem 0x11 src am

end X86Proofs
