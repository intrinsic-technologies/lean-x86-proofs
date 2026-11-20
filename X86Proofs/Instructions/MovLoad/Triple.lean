import X86Proofs.Instructions.MovLoad.Step
import X86Proofs.Instructions.MovLoad.Encode
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Program.Compose

/-!
# `mov r, [mem]` triples

`REX 8B /r` with a memory operand given by an `AddrMode` `am`; the instruction is
`3 + am.tail.length` bytes long and reads the operand at `am.addr s (p + len)` in the start state
`s` (for a RIP-relative operand, relative to the instruction's end `p + len`).

- `mov_r64_m64_triple_of_bytes` (`REX.W 8B /r`), `mov_r64_m64_triple` (`encodeMovR64M64 dst am`:
  destination register number `dst`, REX.W with REX.R/X/B from `dst` and `am`); effect
  `movR64M64Effect`.
- `mov_r32_m32_triple_of_bytes` (`REX 8B /r`, W = 0); effect `movR32M32Effect` (zero-extended).

Precondition: `LoadPre p (fun s => am.addr s (p + len)) (n / 8)`: RIP = `p` and the bytes read
lie below 4 GiB and are present in RAM (they may cross a page). The effect writes only the
destination register: memory, flags and other registers are unchanged.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The length of `rex 8B modrm tail`. -/
abbrev movLoadLen (am : AddrMode) : Nat := 3 + am.tail.length

/-- The effect of `mov dst, qword [am]` at `p`: RIP = `p + len`, `dst` set to the 8 bytes at the
operand's address in the start state. -/
def movR64M64Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (movLoadLen am)
    writes := [⟨(Operand.reg dst : Operand 64),
      (Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 64).read s⟩] }

/-- The effect of `mov dst32, dword [am]` at `p`: RIP = `p + len`, the full register `dst` set to
the 4 bytes at the operand's address, zero-extended. -/
def movR32M32Effect (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (movLoadLen am)
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.mem (am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) : Operand 32).read s).setWidth
        64⟩] }

@[simp] theorem movR64M64Effect_components (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (movR64M64Effect p dst am s).components = [.reg dst, .rip] := rfl

@[simp] theorem movR32M32Effect_components (p : BitVec 64) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) : (movR32M32Effect p dst am s).components = [.reg dst, .rip] := rfl

/-- The step behind `mov_r64_m64_triple_of_bytes`: from a ready state with the instruction in memory
and the precondition, one `step` reaches a ready state with the effect `movR64M64Effect`. -/
theorem mov_r64_m64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (rex :: 0x8B :: am.modrm reg :: am.tail))
      (movR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, mov_r64_m64_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  rfl

/--
The triple for `mov r64, [mem]` (`REX.W 8B /r`, `mod ≠ 3`) at `p`, for any addressing shape `am`
and `reg` field: the effect `movR64M64Effect` on the `reg` register extended by REX.R.
-/
theorem mov_r64_m64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (rex :: 0x8B :: am.modrm reg :: am.tail))
      (Effect.post (movR64M64Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movR64M64Effect_components p _ am s) _)
    (mov_r64_m64_effect_step p rex hrex reg am hv hx hb)

/-- The step behind `mov_r32_m32_triple_of_bytes`: from a ready state with the instruction in memory
and the precondition, one `step` reaches a ready state with the effect `movR32M32Effect`. -/
theorem mov_r32_m32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 4)
      (codeRange p (rex :: 0x8B :: am.modrm reg :: am.tail))
      (movR32M32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  refine ⟨_, mov_r32_m32_step s h rex hrex reg am hv hx hb hcode.bytesAt hlow hread,
    ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]
  rfl

/--
The triple for `mov r32, [mem]` (`REX 8B /r` with W = 0, `mod ≠ 3`) at `p`: the effect
`movR32M32Effect` on the `reg` register extended by REX.R.
-/
theorem mov_r32_m32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 4)
      (codeRange p (rex :: 0x8B :: am.modrm reg :: am.tail))
      (Effect.post (movR32M32Effect p (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movR32M32Effect_components p _ am s) _)
    (mov_r32_m32_effect_step p rex hrex reg am hv hx hb)

/-- The triple for `mov dst, qword [am]` on the 64-bit register numbered `dst` at `p`, in the
encoding `encodeMovR64M64`: the effect `movR64M64Effect` on that register. -/
theorem mov_r64_m64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (movLoadLen am))) 8)
      (codeRange p (encodeMovR64M64 dst am))
      (Effect.post (movR64M64Effect p (dst.setWidth 5) am)) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec dst
  have := mov_r64_m64_triple_of_bytes p _ hrex (regLow dst) am hv hx hb
  rwa [hr, gprNumber_reg] at this

/-! ### Examples: encodings of loads -/

example : encodeMovR64M64 0 (.base 7 (.d8 8)) = [0x48, 0x8B, 0x47, 0x08] := by decide
example : encodeMovR64M64 3 (.base 7 .none) = [0x48, 0x8B, 0x1F] := by decide
example : encodeMovR64M64 5 (.sib 4 none 0 (.d32 0xe0)) =
    [0x48, 0x8B, 0xAC, 0x24, 0xE0, 0x00, 0x00, 0x00] := by decide
example : encodeMovR64M64 15 (.base 6 (.d32 0x90)) = [0x4C, 0x8B, 0xBE, 0x90, 0x00, 0x00, 0x00] := by
  decide
example : encodeMovR64M64 1 (.sib 4 none 0 (.d8 0x10)) = [0x48, 0x8B, 0x4C, 0x24, 0x10] := by
  decide
/-- `mov r8d, [rcx + rdi]` (`44 8B 04 39`): REX.R, SIB with index RDI. -/
example : (0x44 : UInt8) :: 0x8B :: (AddrMode.sib 1 (some 7) 0 .none).modrm 0 ::
    (AddrMode.sib 1 (some 7) 0 .none).tail = [0x44, 0x8B, 0x04, 0x39] := by decide
/-- `mov edi, [r15 + rsi]` (`41 8B 3C 37`): REX.B, base R15. -/
example : (0x41 : UInt8) :: 0x8B :: (AddrMode.sib 15 (some 6) 0 .none).modrm 7 ::
    (AddrMode.sib 15 (some 6) 0 .none).tail = [0x41, 0x8B, 0x3C, 0x37] := by decide
attribute [x86_compose] movR64M64Effect movR32M32Effect movLoadLen

@[x86_local] theorem movR64M64Effect_local {p : BitVec 64} {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (movR64M64Effect p dst am) := by
  effect_local [movR64M64Effect]

@[x86_local] theorem movR32M32Effect_local {p : BitVec 64} {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (movR32M32Effect p dst am) := by
  effect_local [movR32M32Effect]

end X86Proofs
