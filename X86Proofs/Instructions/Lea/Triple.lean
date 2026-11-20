import X86Proofs.Instructions.Lea.Step
import X86Proofs.Instructions.Lea.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

/-!
# `lea r64, [mem]` triples

`REX.W 8D /r` with an addressing shape `am`; the instruction is `3 + am.tail.length` bytes long and
writes `am.addr s (p + len)` (for a RIP-relative operand, relative to the instruction's end
`p + len`) to the destination register.

- `lea_r64_triple_of_bytes` (`REX.W 8D /r`, any REX.W byte whose X and B bits are `am`'s),
  `lea_r64_triple` (`encodeLeaR64M dst am`: destination register number `dst`, REX.W with REX.R/X/B
  from `dst` and `am`); effect `leaR64Effect`.

Precondition: RIP = `p`, nothing about memory (LEA reads none). The effect writes only the
destination register: memory, flags and other registers are unchanged.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The length of `rex 8D modrm tail`. -/
abbrev leaLen (am : AddrMode) : Nat := 3 + am.tail.length

/-- The effect of `lea dst, [am]` at `p`: RIP = `p + len`, `dst` set to the operand's address in
the start state. -/
def leaR64Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (leaLen am)
    writes := [⟨(Operand.reg dst : Operand 64), am.addr s (p + BitVec.ofNat 64 (leaLen am))⟩] }

@[simp] theorem leaR64Effect_components (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (leaR64Effect p dst am s).components = [.reg dst, .rip] := rfl

/-- The step behind `lea_r64_triple_of_bytes`: from a ready state with the instruction in memory and
the precondition, one `step` reaches a ready state with the effect `leaR64Effect`. -/
theorem lea_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x8D :: am.modrm reg :: am.tail))
      (leaR64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode rfl
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, lea_r64_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow,
    ReadyToStep.afterStep_writeResult h _ _ (fun _ => am.addrAt s (3 + am.tail.length)) _,
    ⟨afterStep_writeResult_rip h _ _ (fun _ => am.addrAt s (3 + am.tail.length)) _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ (fun _ => am.addrAt s (3 + am.tail.length)) _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self]
  rfl

/--
The triple for `lea r64, [mem]` (`REX.W 8D /r`, `mod ≠ 3`) at `p`, for any addressing shape `am`
and `reg` field: the effect `leaR64Effect` on the `reg` register extended by REX.R.
-/
theorem lea_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x8D :: am.modrm reg :: am.tail))
      (Effect.post (leaR64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (leaR64Effect_components p _ am s) _)
    (lea_r64_effect_step p rex hrex reg am hv hx hb)

/-- The triple for `lea dst, [am]` on the 64-bit register numbered `dst` at `p`, in the encoding
`encodeLeaR64M`: the effect `leaR64Effect` on that register. -/
theorem lea_r64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeLeaR64M dst am))
      (Effect.post (leaR64Effect p (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := lea_r64_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rwa [hr, gprNumber_reg] at this

/-! ### Examples: `lea` encodings, by shape -/

/-- `lea rbx, [rsp + 0x10]` -/
example : encodeLeaR64M 3 (.sib 4 none 0 (.d8 0x10)) = [0x48, 0x8D, 0x5C, 0x24, 0x10] := by decide
/-- `lea rcx, [rsp + 0x10]` -/
example : encodeLeaR64M 1 (.sib 4 none 0 (.d8 0x10)) = [0x48, 0x8D, 0x4C, 0x24, 0x10] := by decide
/-- `lea rsi, [rsp + 0x10]` -/
example : encodeLeaR64M 6 (.sib 4 none 0 (.d8 0x10)) = [0x48, 0x8D, 0x74, 0x24, 0x10] := by decide
/-- `lea rdi, [rsp + 0xf8]` -/
example : encodeLeaR64M 7 (.sib 4 none 0 (.d32 0xf8)) =
    [0x48, 0x8D, 0xBC, 0x24, 0xF8, 0x00, 0x00, 0x00] := by decide
/-- `lea r12, [rsp + 0xf8]` -/
example : encodeLeaR64M 12 (.sib 4 none 0 (.d32 0xf8)) =
    [0x4C, 0x8D, 0xA4, 0x24, 0xF8, 0x00, 0x00, 0x00] := by decide
/-- `lea rcx, [r15 + r13]` -/
example : encodeLeaR64M 1 (.sib 15 (some 13) 0 .none) = [0x4B, 0x8D, 0x0C, 0x2F] := by decide
/-- `lea rdx, [rsp + rax]` -/
example : encodeLeaR64M 2 (.sib 4 (some 0) 0 .none) = [0x48, 0x8D, 0x14, 0x04] := by decide
/-- `lea rcx, [rsp + rax]` -/
example : encodeLeaR64M 1 (.sib 4 (some 0) 0 .none) = [0x48, 0x8D, 0x0C, 0x04] := by decide
/-- `lea rsi, [rcx + rax]` -/
example : encodeLeaR64M 6 (.sib 1 (some 0) 0 .none) = [0x48, 0x8D, 0x34, 0x01] := by decide
/-- `lea rdx, [r15 + rax]` -/
example : encodeLeaR64M 2 (.sib 15 (some 0) 0 .none) = [0x49, 0x8D, 0x14, 0x07] := by decide
/-- `lea rsi, [rsp + rdi]` -/
example : encodeLeaR64M 6 (.sib 4 (some 7) 0 .none) = [0x48, 0x8D, 0x34, 0x3C] := by decide
/-- `lea rdi, [rbx + rbp]` -/
example : encodeLeaR64M 7 (.sib 3 (some 5) 0 .none) = [0x48, 0x8D, 0x3C, 0x2B] := by decide
/-- `lea r13, [rip + 0x725]` -/
example : encodeLeaR64M 13 (.rip 0x725) = [0x4C, 0x8D, 0x2D, 0x25, 0x07, 0x00, 0x00] := by decide

/-- The RIP-relative `lea r13, [rip + 0x725]` (`4C 8D 2D 25 07 00 00`) at `p`: R13 := the
address of the instruction's end plus `0x725`, i.e. `p + 0x72C`. -/
example [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x4C, 0x8D, 0x2D, 0x25, 0x07, 0x00, 0x00])
      (Effect.post (leaR64Effect p 13 (.rip 0x725))) :=
  lea_r64_triple p 13 (.rip 0x725) trivial

example (p : BitVec 64) (s : RamState) :
    (AddrMode.rip 0x725).addr s (p + BitVec.ofNat 64 (leaLen (.rip 0x725))) = p + 0x72C := by
  simp only [AddrMode.addr, leaLen, AddrMode.tail]
  rw [BitVec.add_assoc]
  rfl

/-- `lea rdi, [rbx + rbp]` (`48 8D 3C 2B`) at `p`: RDI := RBX + RBP. -/
example [Bindings] (p : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p [0x48, 0x8D, 0x3C, 0x2B])
      (Effect.post (leaR64Effect p 7 (.sib 3 (some 5) 0 .none))) :=
  lea_r64_triple p 7 (.sib 3 (some 5) 0 .none) ⟨by decide, by decide⟩
attribute [x86_compose] leaR64Effect leaLen

@[x86_local] theorem leaR64Effect_local {p : BitVec 64} {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (leaR64Effect p dst am) := by
  effect_local [leaR64Effect]

end X86Proofs
