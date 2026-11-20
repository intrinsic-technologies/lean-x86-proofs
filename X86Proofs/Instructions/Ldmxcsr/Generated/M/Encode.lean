import X86Proofs.Instructions.Movups.Encode

namespace X86Proofs

abbrev encodeLdmxcsrM32 (am : AddrMode) : List UInt8 :=
  encodeSseMem 0xAE 2 am

end X86Proofs
