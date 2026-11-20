import X86Proofs.Instructions.Movups.Step
import X86Proofs.Instructions.Movups.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.ReadWrite.Sse
import X86Proofs.Program.Compose

/-!
# MOVUPS triples

`movups xmm, m128` (`0F 10 /r`, `mod ≠ 3`) with a memory operand given by an `AddrMode` `am`: the
destination XMM register (`reg`) becomes the 16 bytes at `am.addr s (p + len)` in the start state
`s` (for a RIP-relative operand, relative to the instruction's end `p + len`); bits 128–511 of its
ZMM register are kept; no flags, no memory written. The precondition is
`SseLoadPre p (fun s => am.addr s (p + len))`: RIP = `p`, SSE enabled, and the 16 bytes readable
(no alignment requirement; they may cross a page). The effect is `movupsXmmM128Effect`.

- `movups_xmm_m128_triple_of_bytes`: `0F 10 modrm tail`, registers 0–7, an address needing no REX
  bit, `len = 3 + am.tail.length`.
- `movups_xmm_m128_rex_triple_of_bytes`: `rex 0F 10 modrm tail`, any register and address,
  `len = 4 + am.tail.length`.
- `movups_xmm_m128_triple`: the register given by number (0–15), in the encoding `encodeMovupsXmmM128`.
- Behind an FS/GS segment-override prefix (`r : SegReg`, `r.prefixByte` first):
  `movups_xmm_m128_seg_triple_of_bytes`, `movups_xmm_m128_rex_seg_triple_of_bytes` and
  `movups_xmm_m128_seg_triple`, with the effect `movupsXmmM128SegEffect` (the read at
  `base + am.addr s (p + len)`) and the precondition `SseLoadPre` at that address plus
  `r.Ready base` (the segment ready, with base `base`).
- Examples on concrete encodings.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The effect of `movups dst, [am]` at `p`, for an encoding of `len` bytes: RIP = `p + len`, the
XMM register `dst` set to the 16 bytes at the operand's address in the start state. -/
def movupsXmmM128Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.xmm dst : Operand 128),
    (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s⟩]

/-- MOVUPS changes the destination XMM register and RIP. -/
@[simp] theorem movupsXmmM128Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : (movupsXmmM128Effect p len dst am s).components = [.xmm dst, .rip] :=
  rfl

/-- MOVUPS writes no memory. -/
theorem movupsXmmM128Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) (code : CodeMap) : (movupsXmmM128Effect p len dst am s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

/-- The step behind `movups_xmm_m128_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `movupsXmmM128Effect`. -/
theorem movups_xmm_m128_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SseLoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
      (codeRange p (0x0F :: 0x10 :: am.modrm reg :: am.tail))
      (movupsXmmM128Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨hp, hsse, hread⟩
  subst hp
  have hlow := hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  simp only [List.length_cons] at hlow
  refine ⟨_, movups_xmm_m128_step s h hsse reg am hv hx hb hcode.bytesAt (by omega) hread,
    ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

/--
The triple for `movups xmm, m128` (`0F 10 /r`, no prefix, `mod ≠ 3`) at `p`, for `reg` 0–7 and
an addressing shape `am` needing no REX bit: the effect `movupsXmmM128Effect` on the `reg` register.
-/
theorem movups_xmm_m128_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SseLoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
      (codeRange p (0x0F :: 0x10 :: am.modrm reg :: am.tail))
      (Effect.post (movupsXmmM128Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => movupsXmmM128Effect_avoids p _ _ am s _)
    (movups_xmm_m128_effect_step p reg am hv hx hb)

/-- The step behind `movups_xmm_m128_rex_triple_of_bytes`: from a ready state with the instruction
in memory and the precondition, one `step` reaches a ready state with the effect `movupsXmmM128Effect`. -/
theorem movups_xmm_m128_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SseLoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
      (codeRange p (rex :: 0x0F :: 0x10 :: am.modrm reg :: am.tail))
      (movupsXmmM128Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  rintro s h hcode ⟨hp, hsse, hread⟩
  subst hp
  have hlow := hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  simp only [List.length_cons] at hlow
  refine ⟨_, movups_xmm_m128_rex_step s h hsse rex hrex reg am hv hx hb hcode.bytesAt (by omega)
    hread, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

/--
The triple for `movups xmm, m128` after a REX prefix (`rex 0F 10 /r`, `mod ≠ 3`) at `p`: the
effect `movupsXmmM128Effect` on the `reg` register extended by REX.R, for any addressing shape `am` with
REX.X and REX.B as it needs.
-/
theorem movups_xmm_m128_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SseLoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
      (codeRange p (rex :: 0x0F :: 0x10 :: am.modrm reg :: am.tail))
      (Effect.post (movupsXmmM128Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => movupsXmmM128Effect_avoids p _ _ am s _)
    (movups_xmm_m128_rex_effect_step p rex hrex reg am hv hx hb)

/--
The triple for `movups dst, [am]` on the XMM register numbered `dst` (0–15) at `p`, in the
encoding `encodeMovupsXmmM128`: the effect `movupsXmmM128Effect` on that register, with the length of that
encoding.
-/
theorem movups_xmm_m128_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SseLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovupsXmmM128 dst am).length)))
      (codeRange p (encodeMovupsXmmM128 dst am))
      (Effect.post (movupsXmmM128Effect p (encodeMovupsXmmM128 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeMovupsXmmM128
  rcases encodeSseMem_spec 0x10 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x0F :: 0x10 :: am.modrm (regLow dst) :: am.tail : List UInt8).length =
        3 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movups_xmm_m128_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := movups_xmm_m128_rex_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (am.rexByte false dst :: 0x0F :: 0x10 :: am.modrm (regLow dst) :: am.tail).length =
        4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

/-! ### Through an FS/GS segment override -/

/-- The effect of `movups dst, r:[am]` at `p` (an FS/GS override `r` whose segment has base
`base`), for an encoding of `len` bytes: as `movupsXmmM128Effect`, reading the 16 bytes at
`base + am.addr s (p + len)`. -/
def movupsXmmM128SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.xmm dst : Operand 128),
    (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s⟩]

@[simp] theorem movupsXmmM128SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (movupsXmmM128SegEffect p len base dst am s).components = [.xmm dst, .rip] :=
  rfl

/-- The step behind `movups_xmm_m128_seg_triple_of_bytes`. -/
theorem movups_xmm_m128_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (fun s => SseLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x10 :: am.modrm reg :: am.tail))
      (movupsXmmM128SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨⟨hp, hsse, hread⟩, hseg, hbase⟩
  subst hp hbase
  have hlow := hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  simp only [List.length_cons] at hlow
  refine ⟨_, movups_xmm_m128_seg_step s h hsse r hseg reg am hv hx hb hcode.bytesAt (by omega)
    hread, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

/-- The triple for `movups xmm, m128` behind an FS/GS prefix (`64`/`65 0F 10 /r`, `mod ≠ 3`) at
`p`, for `reg` 0–7 and an addressing shape needing no REX bit: the precondition adds the segment
`r` ready with base `base`, the 16 bytes read at `base + am.addr s (p + len)`. -/
theorem movups_xmm_m128_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => SseLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x10 :: am.modrm reg :: am.tail))
      (Effect.post (movupsXmmM128SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
    (movups_xmm_m128_seg_effect_step p r base reg am hv hx hb)

/-- The step behind `movups_xmm_m128_rex_seg_triple_of_bytes`. -/
theorem movups_xmm_m128_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => SseLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x10 :: am.modrm reg :: am.tail))
      (movupsXmmM128SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  rintro s h hcode ⟨⟨hp, hsse, hread⟩, hseg, hbase⟩
  subst hp hbase
  have hlow := hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  simp only [List.length_cons] at hlow
  refine ⟨_, movups_xmm_m128_rex_seg_step s h hsse r hseg rex hrex reg am hv hx hb hcode.bytesAt
    (by omega) hread, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

/-- The triple for `movups xmm, m128` behind an FS/GS prefix and a REX prefix
(`64`/`65 rex 0F 10 /r`, `mod ≠ 3`) at `p`: any register and addressing shape. -/
theorem movups_xmm_m128_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => SseLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x10 :: am.modrm reg :: am.tail))
      (Effect.post (movupsXmmM128SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
    (movups_xmm_m128_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

/-- The triple for `movups dst, r:[am]` on the XMM register numbered `dst` (0–15) at `p`, in the
encoding `r.prefixByte :: encodeMovupsXmmM128 dst am`. -/
theorem movups_xmm_m128_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => SseLoadPre p (fun t => base + am.addr t
        (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovupsXmmM128 dst am).length)) s ∧
        r.Ready base s)
      (codeRange p (r.prefixByte :: encodeMovupsXmmM128 dst am))
      (Effect.post (movupsXmmM128SegEffect p (r.prefixByte :: encodeMovupsXmmM128 dst am).length
        base (dst.setWidth 5) am)) := by
  unfold encodeMovupsXmmM128
  rcases encodeSseMem_spec 0x10 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0x0F :: 0x10 :: am.modrm (regLow dst) :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact movups_xmm_m128_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := movups_xmm_m128_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow dst) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: am.rexByte false dst :: 0x0F :: 0x10 :: am.modrm (regLow dst) ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

/-! ### Examples -/

/-- `0F 10 01`: `movups xmm0, [rcx]`. -/
example [Bindings] (p : BitVec 64) :
    Triple (SseLoadPre p (fun s => (AddrMode.base 1 .none).addr s (p + 3)))
      (codeRange p [0x0F, 0x10, 0x01])
      (Effect.post (movupsXmmM128Effect p 3 0 (.base 1 .none))) :=
  movups_xmm_m128_triple_of_bytes p 0 (.base 1 .none) ⟨by decide, fun _ => by decide⟩ rfl rfl

/-- `0F 10 49 10`: `movups xmm1, [rcx + 0x10]`. -/
example [Bindings] (p : BitVec 64) :
    Triple (SseLoadPre p (fun s => (AddrMode.base 1 (.d8 0x10)).addr s (p + 4)))
      (codeRange p [0x0F, 0x10, 0x49, 0x10])
      (Effect.post (movupsXmmM128Effect p 4 1 (.base 1 (.d8 0x10)))) :=
  movups_xmm_m128_triple_of_bytes p 1 (.base 1 (.d8 0x10)) ⟨by decide, fun _ => by decide⟩ rfl rfl

/-- `0F 10 81 80 00 00 00`: `movups xmm0, [rcx + 0x80]`. -/
example [Bindings] (p : BitVec 64) :
    Triple (SseLoadPre p (fun s => (AddrMode.base 1 (.d32 0x80)).addr s (p + 7)))
      (codeRange p [0x0F, 0x10, 0x81, 0x80, 0x00, 0x00, 0x00])
      (Effect.post (movupsXmmM128Effect p 7 0 (.base 1 (.d32 0x80)))) :=
  movups_xmm_m128_triple_of_bytes p 0 (.base 1 (.d32 0x80)) ⟨by decide, fun _ => by decide⟩ rfl rfl

/-- `41 0F 10 04 0F`: `movups xmm0, [r15 + rcx]` (REX.B). -/
example [Bindings] (p : BitVec 64) :
    Triple (SseLoadPre p (fun s => (AddrMode.sib 15 (some 1) 0 .none).addr s (p + 5)))
      (codeRange p [0x41, 0x0F, 0x10, 0x04, 0x0F])
      (Effect.post (movupsXmmM128Effect p 5 0 (.sib 15 (some 1) 0 .none))) :=
  movups_xmm_m128_rex_triple_of_bytes p 0x41 (by unfold RexPrefix; decide) 0
    (.sib 15 (some 1) 0 .none) ⟨by decide, fun _ => by decide⟩ (by decide) (by decide)

/-- `41 0F 10 4C 0F 10`: `movups xmm1, [r15 + rcx + 0x10]`. -/
example [Bindings] (p : BitVec 64) :
    Triple (SseLoadPre p (fun s => (AddrMode.sib 15 (some 1) 0 (.d8 0x10)).addr s (p + 6)))
      (codeRange p [0x41, 0x0F, 0x10, 0x4C, 0x0F, 0x10])
      (Effect.post (movupsXmmM128Effect p 6 1 (.sib 15 (some 1) 0 (.d8 0x10)))) :=
  movups_xmm_m128_rex_triple_of_bytes p 0x41 (by unfold RexPrefix; decide) 1
    (.sib 15 (some 1) 0 (.d8 0x10)) ⟨by decide, fun _ => by decide⟩ (by decide) (by decide)

/-- `encodeMovupsXmmM128` gives the expected bytes. -/
example : encodeMovupsXmmM128 0 (.base 1 .none) = [0x0F, 0x10, 0x01] := by decide
example : encodeMovupsXmmM128 1 (.base 1 (.d32 0x90)) = [0x0F, 0x10, 0x89, 0x90, 0x00, 0x00, 0x00] := by
  decide
example : encodeMovupsXmmM128 1 (.sib 15 (some 1) 0 (.d8 0x10)) = [0x41, 0x0F, 0x10, 0x4C, 0x0F, 0x10] := by
  decide
attribute [x86_compose] movupsXmmM128Effect

@[x86_local] theorem movupsXmmM128Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (movupsXmmM128Effect p len dst am) := by
  effect_local [movupsXmmM128Effect]

attribute [x86_compose] movupsXmmM128SegEffect

@[x86_local] theorem movupsXmmM128SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (movupsXmmM128SegEffect p len base dst am) := by
  effect_local [movupsXmmM128SegEffect]

end X86Proofs
