import X86Proofs.Step.Address

/-!
# Encoding legacy SSE loads

The standard bytes of a legacy SSE instruction `0F op /r` with an XMM register given by number
and any `AddrMode` (`encodeSseMem`, shared with XORPS), in the shortest encoding, and
`movups xmm, [mem]` (`0F 10`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The bytes of a legacy SSE instruction `0F op /r` on XMM register `dst` (0–15) with
addressing `am`, in the shortest encoding: no prefix if `dst` is 0–7 and `am` needs no REX bit,
else a REX prefix (`am.rexByte false dst`). -/
def encodeSseMem (op : UInt8) (dst : BitVec 4) (am : AddrMode) : List UInt8 :=
  if am.NoRex dst then 0x0F :: op :: am.modrm (regLow dst) :: am.tail
  else am.rexByte false dst :: 0x0F :: op :: am.modrm (regLow dst) :: am.tail

/-- The bytes of `movups dst, [am]` (`encodeSseMem 0x10`). E.g.
`encodeMovupsXmmM128 0 (.base 1 .none) = [0x0F, 0x10, 0x01]` (`movups xmm0, [rcx]`). -/
abbrev encodeMovupsXmmM128 (dst : BitVec 4) (am : AddrMode) : List UInt8 := encodeSseMem 0x10 dst am

/-- `encodeSseMem` is a valid encoding of the register and address it names. -/
theorem encodeSseMem_spec (op : UInt8) (dst : BitVec 4) (am : AddrMode) :
    (encodeSseMem op dst am = 0x0F :: op :: am.modrm (regLow dst) :: am.tail ∧
      am.rexX = 0 ∧ am.rexB = 0 ∧ gprNumber 0 0 (regLow dst) = dst.setWidth 5) ∨
    (encodeSseMem op dst am = am.rexByte false dst :: 0x0F :: op :: am.modrm (regLow dst) :: am.tail) := by
  unfold encodeSseMem
  by_cases hc : am.NoRex dst
  · refine .inl ⟨ite_eq_left hc, hc.2.1, hc.2.2, ?_⟩
    have := gprNumber_reg dst
    rwa [hc.1] at this
  · exact .inr (ite_eq_right hc)

theorem encodeSseMem_length (op : UInt8) (dst : BitVec 4) (am : AddrMode) :
    (encodeSseMem op dst am).length = 3 + am.tail.length ∨
      (encodeSseMem op dst am).length = 4 + am.tail.length := by
  unfold encodeSseMem; split <;> simp <;> omega

end X86Proofs
