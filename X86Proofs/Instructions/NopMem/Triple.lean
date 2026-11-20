import X86Proofs.Instructions.NopMem.Step
import X86Proofs.Instructions.NopMem.Encode
import X86Proofs.Instructions.Nop.Triple

/-!
# Multi-byte NOP triples

`pre 0F 1F /0` with a memory operand (`encodeNopM pre am`), `pre` a run of `66` / `2E` prefixes:
effect `nopEffect p (nopMemLen pre am)` (RIP only), precondition RIP = `p` (the operand is never
read).

- `nop_m_triple_of_bytes`: for any such prefix run (at most 7) and addressing shape without
  REX.B/X.
- `nop_m_triple`: the same with the bytes and the length given as concrete values (checked by
  `decide`), for stating triples on literal code.

Examples: multi-byte NOP encodings from 3 to 13 bytes.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The step behind `nop_m_triple_of_bytes`: from a ready state with the instruction in memory and
the precondition, one `step` reaches a ready state with the effect `nopEffect`. -/
theorem nop_m_effect_step [Bindings] (p : BitVec 64) (pre : List UInt8)
    (hpre : ∀ q ∈ pre, NopPrefix q) (hlen : pre.length ≤ 7) (am : AddrMode) (hv : am.Valid)
    (hb : am.rexB = 0) (hx : am.rexX = 0) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeNopM pre am))
      (fun _ => nopEffect p (nopMemLen pre am)) := by
  rintro s h hcode rfl
  have hl := hcode.low (by simp [encodeNopM]; omega) (by
    have := am.tail_length_le
    simp [encodeNopM]; omega)
  simp only [encodeNopM, List.length_append, List.length_cons] at hl
  exact ⟨_, nop_m_step s h pre hpre hlen am hv hb hx hcode.bytesAt
      (by simp only [nopMemLen]; omega),
    ReadyToStep.afterStep_withNextIP h _ _, nopEffect_holds h _⟩

/-- The triple for the multi-byte NOP `pre 0F 1F /0` (`mod ≠ 3`) at `p`: only RIP moves, to
`p + nopMemLen pre am`. -/
theorem nop_m_triple_of_bytes [Bindings] (p : BitVec 64) (pre : List UInt8)
    (hpre : ∀ q ∈ pre, NopPrefix q) (hlen : pre.length ≤ 7) (am : AddrMode) (hv : am.Valid)
    (hb : am.rexB = 0) (hx : am.rexX = 0) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeNopM pre am))
      (Effect.post fun _ => nopEffect p (nopMemLen pre am)) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p _ _)
    (nop_m_effect_step p pre hpre hlen am hv hb hx)

/-- `nop_m_triple_of_bytes` with the code and the length as given values: `bytes` must be
`encodeNopM pre am` and `len` its length (both closed by `decide` / `rfl` on concrete
encodings). -/
theorem nop_m_triple [Bindings] (p : BitVec 64) (pre : List UInt8) (am : AddrMode)
    (bytes : List UInt8) (len : Nat) (hpre : ∀ q ∈ pre, NopPrefix q) (hlen : pre.length ≤ 7)
    (hv : am.Valid) (hb : am.rexB = 0) (hx : am.rexX = 0) (hbytes : encodeNopM pre am = bytes)
    (hl : nopMemLen pre am = len) :
    Triple (fun s => s.RIP = p) (codeRange p bytes) (Effect.post fun _ => nopEffect p len) := by
  subst hbytes hl
  exact nop_m_triple_of_bytes p pre hpre hlen am hv hb hx

/-! ### Examples: multi-byte NOPs

`0F 1F` memory NOPs as compilers emit them for padding, with their addressing shapes (all on
RAX). -/

section
variable [Bindings] (p : BitVec 64)

/-- `nopl (%rax)`: `0F 1F 00`. -/
example : Triple (fun s => s.RIP = p) (codeRange p [0x0F, 0x1F, 0x00])
    (Effect.post fun _ => nopEffect p 3) :=
  nop_m_triple p [] (.base 0 .none) _ _ (by decide) (by decide)
    ⟨by decide, fun _ => by decide⟩ rfl rfl (by decide) rfl

/-- `nopl 0x0(%rax)`: `0F 1F 40 00`. -/
example : Triple (fun s => s.RIP = p) (codeRange p [0x0F, 0x1F, 0x40, 0x00])
    (Effect.post fun _ => nopEffect p 4) :=
  nop_m_triple p [] (.base 0 (.d8 0)) _ _ (by decide) (by decide)
    ⟨by decide, fun h => by cases h⟩ rfl rfl (by decide) rfl

/-- `nopl 0x0(%rax,%rax,1)`: `0F 1F 44 00 00`. -/
example : Triple (fun s => s.RIP = p) (codeRange p [0x0F, 0x1F, 0x44, 0x00, 0x00])
    (Effect.post fun _ => nopEffect p 5) :=
  nop_m_triple p [] (.sib 0 (some 0) 0 (.d8 0)) _ _ (by decide) (by decide)
    ⟨by decide, fun h => by cases h⟩ rfl rfl (by decide) rfl

/-- `nopl 0x0(%rax)` with a 32-bit displacement: `0F 1F 80 00 00 00 00`. -/
example : Triple (fun s => s.RIP = p) (codeRange p [0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00])
    (Effect.post fun _ => nopEffect p 7) :=
  nop_m_triple p [] (.base 0 (.d32 0)) _ _ (by decide) (by decide)
    ⟨by decide, fun h => by cases h⟩ rfl rfl (by decide) rfl

/-- `nopl 0x0(%rax,%rax,1)` with a 32-bit displacement: `0F 1F 84 00 00 00 00 00`. -/
example : Triple (fun s => s.RIP = p)
    (codeRange p [0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00])
    (Effect.post fun _ => nopEffect p 8) :=
  nop_m_triple p [] (.sib 0 (some 0) 0 (.d32 0)) _ _ (by decide) (by decide)
    ⟨by decide, fun h => by cases h⟩ rfl rfl (by decide) rfl

/-- `nopw 0x0(%rax,%rax,1)`: `66 0F 1F 84 00 00 00 00 00`. -/
example : Triple (fun s => s.RIP = p)
    (codeRange p [0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00])
    (Effect.post fun _ => nopEffect p 9) :=
  nop_m_triple p [0x66] (.sib 0 (some 0) 0 (.d32 0)) _ _ (by decide) (by decide)
    ⟨by decide, fun h => by cases h⟩ rfl rfl (by decide) rfl

/-- `cs nopw 0x0(%rax,%rax,1)`: `66 2E 0F 1F 84 00 00 00 00 00`. -/
example : Triple (fun s => s.RIP = p)
    (codeRange p [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00])
    (Effect.post fun _ => nopEffect p 10) :=
  nop_m_triple p [0x66, 0x2E] (.sib 0 (some 0) 0 (.d32 0)) _ _ (by decide) (by decide)
    ⟨by decide, fun h => by cases h⟩ rfl rfl (by decide) rfl

/-- `data16 data16 cs nopw 0x0(%rax,%rax,1)`: `66 66 66 2E 0F 1F 84 00 00 00 00 00`. -/
example : Triple (fun s => s.RIP = p)
    (codeRange p [0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00])
    (Effect.post fun _ => nopEffect p 12) :=
  nop_m_triple p [0x66, 0x66, 0x66, 0x2E] (.sib 0 (some 0) 0 (.d32 0)) _ _ (by decide)
    (by decide) ⟨by decide, fun h => by cases h⟩ rfl rfl (by decide) rfl

/-- `data16 data16 data16 cs nopw 0x0(%rax,%rax,1)`: `66 66 66 66 2E 0F 1F 84 00 00 00 00 00`,
13 bytes. -/
example : Triple (fun s => s.RIP = p)
    (codeRange p [0x66, 0x66, 0x66, 0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00])
    (Effect.post fun _ => nopEffect p 13) :=
  nop_m_triple p [0x66, 0x66, 0x66, 0x66, 0x2E] (.sib 0 (some 0) 0 (.d32 0)) _ _ (by decide)
    (by decide) ⟨by decide, fun h => by cases h⟩ rfl rfl (by decide) rfl

end

end X86Proofs
