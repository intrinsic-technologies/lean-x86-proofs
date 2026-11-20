import X86Proofs.Instructions.Nop.Generated.M18r7.Step
import X86Proofs.Instructions.Nop.Generated.M18r7.Encode
import X86Proofs.Instructions.Nop.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

theorem nop_18r7_m_effect_step [Bindings] (p : BitVec 64) (pre : List UInt8)
    (hpre : ∀ q ∈ pre, NopPrefix q) (hlen : pre.length ≤ 7) (am : AddrMode) (hv : am.Valid)
    (hb : am.rexB = 0) (hx : am.rexX = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeNop18R7M pre am))
      (fun _ => nopEffect p (nopMemLen pre am)) := by
  rintro s h hcode rfl
  have hl := hcode.low (by simp [encodeNop18R7M]; omega) (by
    have := am.tail_length_le
    simp [encodeNop18R7M]; omega)
  simp only [encodeNop18R7M, List.length_append, List.length_cons] at hl
  exact ⟨_, nop_18r7_m_step s h pre hpre hlen am hv hb hx hcode.bytesAt
      (by simp only [nopMemLen]; omega),
    ReadyToStep.afterStep_withNextIP h _ _, nopEffect_holds h _⟩

theorem nop_18r7_m_triple_of_bytes [Bindings] (p : BitVec 64) (pre : List UInt8)
    (hpre : ∀ q ∈ pre, NopPrefix q) (hlen : pre.length ≤ 7) (am : AddrMode) (hv : am.Valid)
    (hb : am.rexB = 0) (hx : am.rexX = 0) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNop18R7M pre am))
      (Effect.post fun _ => nopEffect p (nopMemLen pre am)) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p _ _)
    (nop_18r7_m_effect_step p pre hpre hlen am hv hb hx)

theorem nop_18r7_m_triple [Bindings] (p : BitVec 64) (pre : List UInt8) (am : AddrMode)
    (bytes : List UInt8) (len : Nat) (hpre : ∀ q ∈ pre, NopPrefix q) (hlen : pre.length ≤ 7)
    (hv : am.Valid) (hb : am.rexB = 0) (hx : am.rexX = 0)
    (hbytes : encodeNop18R7M pre am = bytes) (hl : nopMemLen pre am = len) :
    Triple (fun s => s.RIP = p) (codeRange p bytes) (Effect.post fun _ => nopEffect p len) := by
  subst hbytes hl
  exact nop_18r7_m_triple_of_bytes p pre hpre hlen am hv hb hx

end X86Proofs
