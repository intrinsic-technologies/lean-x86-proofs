import X86Proofs.Instructions.Mov.Step
import X86Proofs.Instructions.Mov.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

/-!
# MOV triples

Per encoding, the step with its effect (`_effect_step`, a `StepEffect`, from its step theorem and
preservation theorem) and a triple for any bytes of that encoding, derived from it by
`Triple.of_effect`; per operand size, the same for registers given by
number (and the immediate as a value), so a program proof never decodes REX, ModRM or opcode
bits itself.

`mov r/m, r` (`89 /r`, both operands registers):
- `mov_r64_r64_triple_of_bytes` (`REX.W 89 /r`), `mov_r64_r64_triple` (`encodeMovR64R64`); effect
  `movR64R64Effect`.
- `mov_r32_r32_triple_of_bytes` (`89 /r`), `mov_r32_r32_rex_triple_of_bytes` (`REX 89 /r`, W = 0),
  `mov_r32_r32_triple` (`encodeMovR32R32`); effect `movR32R32Effect`.

`mov r, imm` (`B8+r`):
- `mov_r32_imm32_triple_of_bytes` (`B8+r imm32`), `mov_r32_imm32_rex_triple_of_bytes`
  (`REX B8+r imm32`, W = 0), `mov_r32_imm32_triple` (`encodeMovR32Imm32`); effect
  `movR32Imm32Effect`.
- `mov_r64_imm64_triple_of_bytes` (`REX.W B8+r imm64`), `mov_r64_imm64_triple`
  (`encodeMovR64Imm64`); effect `movR64Imm64Effect`.

`mov r/m64, imm32` (`C7 /0`, `mod = 3`):
- `mov_r64_imm32_triple_of_bytes` (`REX.W C7 /0 imm32`), `mov_r64_imm32_triple`
  (`encodeMovR64Imm32`); effect `movR64Imm32Effect`, the immediate sign-extended.

MOV sets no flags: every effect has `flags := none`, so its frame (`AgreesExcept`) keeps the
flags. A 32-bit write sets the full 64-bit register to the zero-extended value.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-! ### Effects -/

/-- The effect of `mov dst, src` on 64-bit registers at `p`, from state `s`: RIP = `p + 3`,
`dst` set to the old `src`. -/
def movR64R64Effect (p : BitVec 64) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + 3
    writes := [⟨(Operand.reg dst : Operand 64), (Operand.reg src : Operand 64).read s⟩] }

/-- The effect of `mov dst, src` on 32-bit registers at `p`, for an encoding of `len` bytes (2
without a REX prefix, 3 with one), from state `s`: RIP = `p + len`, the full 64-bit register
`dst` set to the old low half of `src`, zero-extended. -/
def movR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((Operand.reg src : Operand 32).read s).setWidth 64⟩] }

/-- The effect of `mov dst, imm` (32-bit register, `B8+r imm32`) at `p`, for an encoding of `len`
bytes (5 without a REX prefix, 6 with one): RIP = `p + len`, the full 64-bit register `dst` set
to `imm` zero-extended. -/
def movR32Imm32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32)
    (_ : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64), imm.setWidth 64⟩] }

/-- The effect of `mov dst, imm` (64-bit register, `REX.W B8+r imm64`) at `p`: RIP = `p + 10`,
`dst` set to `imm`. -/
def movR64Imm64Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 64) (_ : RamState) :
    Effect :=
  { rip := p + 10
    writes := [⟨(Operand.reg dst : Operand 64), imm⟩] }

/-- The effect of `mov dst, imm` (64-bit register, `REX.W C7 /0 imm32`) at `p`: RIP = `p + 7`,
`dst` set to `imm` sign-extended to 64 bits. -/
def movR64Imm32Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (_ : RamState) :
    Effect :=
  { rip := p + 7
    writes := [⟨(Operand.reg dst : Operand 64), imm.signExtend 64⟩] }

/-- MOV between registers changes the destination register and RIP. -/
@[simp] theorem movR64R64Effect_components (p : BitVec 64) (dst src : BitVec 5) (s : RamState) :
    (movR64R64Effect p dst src s).components = [.reg dst, .rip] := rfl

@[simp] theorem movR32R32Effect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (movR32R32Effect p len dst src s).components = [.reg dst, .rip] := rfl

/-- MOV of an immediate changes the destination register and RIP. -/
@[simp] theorem movR32Imm32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (imm : BitVec 32) (s : RamState) :
    (movR32Imm32Effect p len dst imm s).components = [.reg dst, .rip] := rfl

@[simp] theorem movR64Imm64Effect_components (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 64)
    (s : RamState) : (movR64Imm64Effect p dst imm s).components = [.reg dst, .rip] := rfl

@[simp] theorem movR64Imm32Effect_components (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32)
    (s : RamState) : (movR64Imm32Effect p dst imm s).components = [.reg dst, .rip] := rfl

/-- An effect that changes one register and RIP writes no memory, so it avoids any code. -/
theorem Effect.avoids_of_components_reg_rip {e : Effect} {r : BitVec 5}
    (h : e.components = [.reg r, .rip]) (code : CodeMap) : e.Avoids code :=
  Effect.Avoids.of_noMem (by rw [h]; simp [Component.Covers]) code

/-! ### `89 /r` -/

/-- The step behind `mov_r64_r64_triple_of_bytes`: from a ready state with the instruction in memory
and the precondition, one `step` reaches a ready state with the effect `movR64R64Effect`. -/
theorem mov_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x89, modrm])
      (movR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, mov_r64_r64_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), mov_r64_r64_ready h rex modrm,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial, AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

/--
The triple for `mov r/m64, r64` (`REX.W 89 /r`, `mod = 3`) at address `p`, for any encoding: the
effect `movR64R64Effect` on the destination (`rm` extended by REX.B) and the source (`reg`
extended by REX.R).
-/
theorem mov_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x89, modrm])
      (Effect.post (movR64R64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movR64R64Effect_components p _ _ s) _)
    (mov_r64_r64_effect_step p rex modrm hrex hmod)

/-- The step behind `mov_r32_r32_triple_of_bytes`: from a ready state with the instruction in memory
and the precondition, one `step` reaches a ready state with the effect `movR32R32Effect`. -/
theorem mov_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x89, modrm])
      (movR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, mov_r32_r32_step s h modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), mov_r32_r32_ready h modrm,
    ⟨afterStep_writeResult_rip h 2 _ _ _, ?_, trivial, AgreesExcept.afterStep_writeResult s 2 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

/--
The triple for `mov r/m32, r32` (`89 /r` with no prefix, `mod = 3`) at address `p`, for any
encoding: the effect `movR32R32Effect` on the destination (`rm`) and the source (`reg`).
-/
theorem mov_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [0x89, modrm])
      (Effect.post (movR32R32Effect p 2 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movR32R32Effect_components p _ _ _ s) _)
    (mov_r32_r32_effect_step p modrm hmod)

/-- The step behind `mov_r32_r32_rex_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `movR32R32Effect`. -/
theorem mov_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x89, modrm])
      (movR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  rintro s h hcode rfl
  refine ⟨_, mov_r32_r32_rex_step s h rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), mov_r32_r32_rex_ready h rex modrm,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial, AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec, Operand.read_afterFetches,
    Operand.read_beforeFetch]

/--
The triple for `mov r/m32, r32` (`REX 89 /r` with W = 0, `mod = 3`) at address `p`, for any
encoding: the effect `movR32R32Effect` on the destination (`rm` extended by REX.B) and the source
(`reg` extended by REX.R).
-/
theorem mov_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p) (codeRange p [rex, 0x89, modrm])
      (Effect.post (movR32R32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movR32R32Effect_components p _ _ _ s) _)
    (mov_r32_r32_rex_effect_step p rex modrm hrex hmod)

/--
The triple for `mov dst, src` on 64-bit registers numbered `dst` and `src` (0–15) at address
`p`: the effect `movR64R64Effect` on those registers.
-/
theorem mov_r64_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR64R64 dst src))
      (Effect.post (movR64R64Effect p (dst.setWidth 5) (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeMovR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact mov_r64_r64_triple_of_bytes p rex modrm hrex hmod

/--
The triple for `mov dst, src` on 32-bit registers numbered `dst` and `src` (0–15) at address
`p`, in the encoding `encodeMovR32R32`: the effect `movR32R32Effect` on those registers, with the
length of that encoding (2 or 3).
-/
theorem mov_r32_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR32R32 dst src))
      (Effect.post (movR32R32Effect p (encodeMovR32R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeMovR32R32_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact mov_r32_r32_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact mov_r32_r32_rex_triple_of_bytes p rex modrm hrex hmod

/-! ### `B8+r` -/

/-- The step behind `mov_r32_imm32_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `movR32Imm32Effect`.
-/
theorem mov_r32_imm32_effect_step [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : MovImmOpcode op) (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (op :: immBytes 32 imm))
      (movR32Imm32Effect p 5 (gprNumber 0 0 (opcodeReg op)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, mov_r32_imm32_step s h op hop imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), mov_r32_imm32_ready h op imm,
    ⟨afterStep_writeResult_rip h 5 _ _ _, ?_, trivial, AgreesExcept.afterStep_writeResult s 5 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec]

/--
The triple for `mov r32, imm32` (`B8+r imm32` with no prefix) at address `p`, for any opcode
`B8`–`BF` and immediate `imm`: the effect `movR32Imm32Effect` on register `op & 7`.
-/
theorem mov_r32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : MovImmOpcode op) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (op :: immBytes 32 imm))
      (Effect.post (movR32Imm32Effect p 5 (gprNumber 0 0 (opcodeReg op)) imm)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movR32Imm32Effect_components p _ _ _ s) _)
    (mov_r32_imm32_effect_step p op hop imm)

/-- The step behind `mov_r32_imm32_rex_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `movR32Imm32Effect`.
-/
theorem mov_r32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hop : MovImmOpcode op) (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: op :: immBytes 32 imm))
      (movR32Imm32Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
        imm) := by
  rintro s h hcode rfl
  refine ⟨_, mov_r32_imm32_rex_step s h rex op hrex hop imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), mov_r32_imm32_rex_ready h rex op imm,
    ⟨afterStep_writeResult_rip h 6 _ _ _, ?_, trivial, AgreesExcept.afterStep_writeResult s 6 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec]

/--
The triple for `mov r32, imm32` (`REX B8+r imm32` with W = 0) at address `p`: the effect
`movR32Imm32Effect` on register `op & 7` extended by REX.B.
-/
theorem mov_r32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hop : MovImmOpcode op) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: op :: immBytes 32 imm))
      (Effect.post (movR32Imm32Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
        imm)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movR32Imm32Effect_components p _ _ _ s) _)
    (mov_r32_imm32_rex_effect_step p rex op hrex hop imm)

/--
The triple for `mov dst, imm` on the 32-bit register numbered `dst` (0–15) at address `p`, in the
encoding `encodeMovR32Imm32`: the effect `movR32Imm32Effect` on that register, with the length of
that encoding (5 or 6).
-/
theorem mov_r32_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR32Imm32 dst imm))
      (Effect.post (movR32Imm32Effect p (encodeMovR32Imm32 dst imm).length (dst.setWidth 5)
        imm)) := by
  rcases encodeMovR32Imm32_spec dst imm with ⟨op, hbytes, hop, hdst⟩ |
    ⟨rex, op, hbytes, hrex, hop, hdst⟩
  · rw [hbytes, ← hdst]
    exact mov_r32_imm32_triple_of_bytes p op hop imm
  · rw [hbytes, ← hdst]
    exact mov_r32_imm32_rex_triple_of_bytes p rex op hrex hop imm

/-- The step behind `mov_r64_imm64_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `movR64Imm64Effect`.
-/
theorem mov_r64_imm64_effect_step [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hop : MovImmOpcode op) (imm : BitVec 64) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: op :: immBytes 64 imm))
      (movR64Imm64Effect p (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
        imm) := by
  rintro s h hcode rfl
  refine ⟨_, mov_r64_imm64_step s h rex op hrex hop imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), mov_r64_imm64_ready h rex op imm,
    ⟨afterStep_writeResult_rip h 10 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 10 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movSpec]

/--
The triple for `mov r64, imm64` (`REX.W B8+r imm64`) at address `p`: the effect
`movR64Imm64Effect` on register `op & 7` extended by REX.B.
-/
theorem mov_r64_imm64_triple_of_bytes [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hop : MovImmOpcode op) (imm : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: op :: immBytes 64 imm))
      (Effect.post (movR64Imm64Effect p (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
        imm)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movR64Imm64Effect_components p _ _ s) _)
    (mov_r64_imm64_effect_step p rex op hrex hop imm)

/-- The triple for `mov dst, imm` on the 64-bit register numbered `dst` (0–15) with a 64-bit
immediate at address `p`: the effect `movR64Imm64Effect` on that register. -/
theorem mov_r64_imm64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 64) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR64Imm64 dst imm))
      (Effect.post (movR64Imm64Effect p (dst.setWidth 5) imm)) := by
  obtain ⟨rex, op, hbytes, hrex, hop, hdst⟩ := encodeMovR64Imm64_spec dst imm
  rw [hbytes, ← hdst]
  exact mov_r64_imm64_triple_of_bytes p rex op hrex hop imm

/-! ### `C7 /0` -/

/-- The step behind `mov_r64_imm32_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `movR64Imm32Effect`.
-/
theorem mov_r64_imm32_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 32) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0xC7 :: modrm :: immBytes 32 imm))
      (movR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        imm) := by
  rintro s h hcode rfl
  refine ⟨_, mov_r64_imm32_step s h rex modrm hrex hmod hreg imm hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), mov_r64_imm32_ready h rex modrm imm,
    ⟨afterStep_writeResult_rip h 7 _ _ _, ?_, trivial, AgreesExcept.afterStep_writeResult s 7 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movSpec]

/--
The triple for `mov r/m64, imm32` with a register operand (`REX.W C7 /0 imm32`, `mod = 3`) at
address `p`: the effect `movR64Imm32Effect` on the `rm` register extended by REX.B.
-/
theorem mov_r64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0xC7 :: modrm :: immBytes 32 imm))
      (Effect.post (movR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        imm)) :=
  Triple.of_effect (fun s _ =>
    Effect.avoids_of_components_reg_rip (movR64Imm32Effect_components p _ _ s) _)
    (mov_r64_imm32_effect_step p rex modrm hrex hmod hreg imm)

/-- The triple for `mov dst, imm` on the 64-bit register numbered `dst` (0–15) with a 32-bit
immediate at address `p`: the effect `movR64Imm32Effect` on that register (the immediate
sign-extended). -/
theorem mov_r64_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovR64Imm32 dst imm))
      (Effect.post (movR64Imm32Effect p (dst.setWidth 5) imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeMovR64Imm32_spec dst imm
  rw [hbytes, ← hdst]
  exact mov_r64_imm32_triple_of_bytes p rex modrm hrex hmod hreg imm
attribute [x86_compose] movR64R64Effect movR32R32Effect movR32Imm32Effect movR64Imm64Effect
  movR64Imm32Effect

@[x86_local] theorem movR64R64Effect_local {p : BitVec 64} {dst src : BitVec 5} :
    Effect.Local (movR64R64Effect p dst src) := by
  effect_local [movR64R64Effect]

@[x86_local] theorem movR32R32Effect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (movR32R32Effect p len dst src) := by
  effect_local [movR32R32Effect]

@[x86_local] theorem movR32Imm32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm32 : BitVec 32} :
    Effect.Local (movR32Imm32Effect p len dst imm32) := by
  effect_local [movR32Imm32Effect]

@[x86_local] theorem movR64Imm64Effect_local {p : BitVec 64} {dst : BitVec 5} {imm64 : BitVec 64} :
    Effect.Local (movR64Imm64Effect p dst imm64) := by
  effect_local [movR64Imm64Effect]

@[x86_local] theorem movR64Imm32Effect_local {p : BitVec 64} {dst : BitVec 5} {imm32 : BitVec 32} :
    Effect.Local (movR64Imm32Effect p dst imm32) := by
  effect_local [movR64Imm32Effect]

end X86Proofs
