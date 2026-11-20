import X86Proofs.Step.Address

/-!
# Encoding `mov r64, [mem]`

The standard bytes of `mov r64, [mem]` (`REX.W 8B /r`) for a register given by number and any
`AddrMode`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The bytes of `mov dst, qword [am]` for the 64-bit register numbered `dst` (0–15): REX.W
(`am.rexByte true dst`), `8B`, ModRM with `reg = dst & 7`, then `am.tail`. E.g.
`encodeMovR64M64 0 (.base 7 (.d8 8)) = [0x48, 0x8B, 0x47, 0x08]` (`mov rax, [rdi + 8]`). -/
def encodeMovR64M64 (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  am.rexByte true dst :: 0x8B :: am.modrm (regLow dst) :: am.tail

end X86Proofs
