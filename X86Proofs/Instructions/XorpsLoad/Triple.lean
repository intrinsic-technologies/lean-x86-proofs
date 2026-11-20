import X86Proofs.Instructions.XorpsLoad.Step
import X86Proofs.Instructions.XorpsLoad.Encode
import X86Proofs.Instructions.Movups.Triple
import X86Proofs.Program.Compose

/-!
# XORPS (memory operand) triples

`xorps xmm, m128` (`0F 57 /r`, `mod ≠ 3`) with a memory operand given by an `AddrMode` `am`: the
destination XMM register (`reg`) becomes its old value xor the 16 bytes at `am.addr s (p + len)`
in the start state `s`; bits 128–511 of its ZMM register are kept; no flags, no memory written.
The operand must be 16-byte aligned (lean-x86's `Explicitly_Aligned`: else #GP), so the
precondition is `SseAlignedLoadPre p (fun s => am.addr s (p + len))`: RIP = `p`, SSE enabled, the
16 bytes readable, and the address a multiple of 16. The effect is `xorpsXmmM128Effect`.

- `xorps_xmm_m128_triple_of_bytes`: `0F 57 modrm tail`, registers 0–7, an address needing no REX
  bit, `len = 3 + am.tail.length`.
- `xorps_xmm_m128_rex_triple_of_bytes`: `rex 0F 57 modrm tail`, any register and address,
  `len = 4 + am.tail.length`.
- `xorps_xmm_m128_triple`: the register given by number (0–15), in the encoding `encodeXorpsXmmM128`.
- Behind an FS/GS segment-override prefix (`r : SegReg`, `r.prefixByte` first):
  `xorps_xmm_m128_seg_triple_of_bytes`, `xorps_xmm_m128_rex_seg_triple_of_bytes` and
  `xorps_xmm_m128_seg_triple`, with the effect `xorpsXmmM128SegEffect` (the operand at
  `base + am.addr s (p + len)`) and the precondition `SseAlignedLoadPre` at that address plus
  `r.Ready base` (the segment ready, with base `base`).
- Examples on concrete encodings.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The effect of `xorps dst, [am]` at `p`, for an encoding of `len` bytes: RIP = `p + len`, the
XMM register `dst` set to its old value xor the 16 bytes at the operand's address, both in the
start state. -/
def xorpsXmmM128Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.xmm dst : Operand 128), (Operand.xmm dst : Operand 128).read s ^^^
    (Operand.mem (am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s⟩]

/-- XORPS changes the destination XMM register and RIP. -/
@[simp] theorem xorpsXmmM128Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) :
    (xorpsXmmM128Effect p len dst am s).components = [.xmm dst, .rip] := rfl

/-- XORPS writes no memory. -/
theorem xorpsXmmM128Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode)
    (s : RamState) (code : CodeMap) : (xorpsXmmM128Effect p len dst am s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

/-- The step behind `xorps_xmm_m128_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `xorpsXmmM128Effect`. -/
theorem xorps_xmm_m128_effect_step [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SseAlignedLoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
      (codeRange p (0x0F :: 0x57 :: am.modrm reg :: am.tail))
      (xorpsXmmM128Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨⟨hp, hsse, hread⟩, halign⟩
  subst hp
  have hlow := hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  simp only [List.length_cons] at hlow
  refine ⟨_, xorps_xmm_m128_step s h hsse reg am hv hx hb hcode.bytesAt (by omega) halign hread,
    ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

/--
The triple for `xorps xmm, m128` (`0F 57 /r`, no prefix, `mod ≠ 3`) at `p`, for `reg` 0–7 and an
addressing shape `am` needing no REX bit: the effect `xorpsXmmM128Effect` on the `reg` register.
-/
theorem xorps_xmm_m128_triple_of_bytes [Bindings] (p : BitVec 64) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SseAlignedLoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))))
      (codeRange p (0x0F :: 0x57 :: am.modrm reg :: am.tail))
      (Effect.post (xorpsXmmM128Effect p (3 + am.tail.length) (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => xorpsXmmM128Effect_avoids p _ _ am s _)
    (xorps_xmm_m128_effect_step p reg am hv hx hb)

/-- The step behind `xorps_xmm_m128_rex_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `xorpsXmmM128Effect`. -/
theorem xorps_xmm_m128_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SseAlignedLoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
      (codeRange p (rex :: 0x0F :: 0x57 :: am.modrm reg :: am.tail))
      (xorpsXmmM128Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  rintro s h hcode ⟨⟨hp, hsse, hread⟩, halign⟩
  subst hp
  have hlow := hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  simp only [List.length_cons] at hlow
  refine ⟨_, xorps_xmm_m128_rex_step s h hsse rex hrex reg am hv hx hb hcode.bytesAt (by omega)
    halign hread, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

/--
The triple for `xorps xmm, m128` after a REX prefix (`rex 0F 57 /r`, `mod ≠ 3`) at `p`: the
effect `xorpsXmmM128Effect` on the `reg` register extended by REX.R, for any addressing shape `am`
with REX.X and REX.B as it needs.
-/
theorem xorps_xmm_m128_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SseAlignedLoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))))
      (codeRange p (rex :: 0x0F :: 0x57 :: am.modrm reg :: am.tail))
      (Effect.post (xorpsXmmM128Effect p (4 + am.tail.length) (gprNumber 0 (rexR rex.toBitVec) reg)
        am)) :=
  Triple.of_effect (fun s _ => xorpsXmmM128Effect_avoids p _ _ am s _)
    (xorps_xmm_m128_rex_effect_step p rex hrex reg am hv hx hb)

/--
The triple for `xorps dst, [am]` on the XMM register numbered `dst` (0–15) at `p`, in the
encoding `encodeXorpsXmmM128`: the effect `xorpsXmmM128Effect` on that register, with the length of that
encoding.
-/
theorem xorps_xmm_m128_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (SseAlignedLoadPre p
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeXorpsXmmM128 dst am).length)))
      (codeRange p (encodeXorpsXmmM128 dst am))
      (Effect.post (xorpsXmmM128Effect p (encodeXorpsXmmM128 dst am).length (dst.setWidth 5) am)) := by
  unfold encodeXorpsXmmM128
  rcases encodeSseMem_spec 0x57 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (0x0F :: 0x57 :: am.modrm (regLow dst) :: am.tail : List UInt8).length =
        3 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact xorps_xmm_m128_triple_of_bytes p (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := xorps_xmm_m128_rex_triple_of_bytes p _ hrex.rexPrefix (regLow dst) am hv hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (am.rexByte false dst :: 0x0F :: 0x57 :: am.modrm (regLow dst) :: am.tail).length =
        4 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

/-! ### Through an FS/GS segment override -/

/-- The effect of `xorps dst, r:[am]` at `p` (an FS/GS override `r` whose segment has base
`base`), for an encoding of `len` bytes: as `xorpsXmmM128Effect`, with the 16 bytes at
`base + am.addr s (p + len)`. -/
def xorpsXmmM128SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (dst : BitVec 5)
    (am : AddrMode) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.xmm dst : Operand 128), (Operand.xmm dst : Operand 128).read s ^^^
    (Operand.mem (base + am.addr s (p + BitVec.ofNat 64 len)) : Operand 128).read s⟩]

@[simp] theorem xorpsXmmM128SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (dst : BitVec 5) (am : AddrMode) (s : RamState) :
    (xorpsXmmM128SegEffect p len base dst am s).components = [.xmm dst, .rip] :=
  rfl

/-- The step behind `xorps_xmm_m128_seg_triple_of_bytes`. -/
theorem xorps_xmm_m128_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    StepEffect (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x57 :: am.modrm reg :: am.tail))
      (xorpsXmmM128SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am) := by
  rintro s h hcode ⟨⟨⟨hp, hsse, hread⟩, halign⟩, hseg, hbase⟩
  subst hp hbase
  have hlow := hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  simp only [List.length_cons] at hlow
  refine ⟨_, xorps_xmm_m128_seg_step s h hsse r hseg reg am hv hx hb hcode.bytesAt (by omega)
    halign hread, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

/-- The triple for `xorps xmm, m128` behind an FS/GS prefix (`64`/`65 0F 10 /r`, `mod ≠ 3`) at
`p`, for `reg` 0–7 and an addressing shape needing no REX bit: the precondition adds the segment
`r` ready with base `base`, the 16 bytes at `base + am.addr s (p + len)`, 16-byte aligned. -/
theorem xorps_xmm_m128_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0)
    (hb : am.rexB = 0) :
    Triple (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (4 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: 0x0F :: 0x57 :: am.modrm reg :: am.tail))
      (Effect.post (xorpsXmmM128SegEffect p (4 + am.tail.length) base (gprNumber 0 0 reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
    (xorps_xmm_m128_seg_effect_step p r base reg am hv hx hb)

/-- The step behind `xorps_xmm_m128_rex_seg_triple_of_bytes`. -/
theorem xorps_xmm_m128_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x57 :: am.modrm reg :: am.tail))
      (xorpsXmmM128SegEffect p (5 + am.tail.length) base (gprNumber 0 (rexR rex.toBitVec) reg)
        am) := by
  rintro s h hcode ⟨⟨⟨hp, hsse, hread⟩, halign⟩, hseg, hbase⟩
  subst hp hbase
  have hlow := hcode.low (by simp) (by simp; have := am.tail_length_le; omega)
  simp only [List.length_cons] at hlow
  refine ⟨_, xorps_xmm_m128_rex_seg_step s h hsse r hseg rex hrex reg am hv hx hb hcode.bytesAt
    (by omega) halign hread, ReadyToStep.afterStep_load_xmm h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load_xmm s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_load_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  rfl

/-- The triple for `xorps xmm, m128` behind an FS/GS prefix and a REX prefix
(`64`/`65 rex 0F 10 /r`, `mod ≠ 3`) at `p`: any register and addressing shape. -/
theorem xorps_xmm_m128_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8) (hrex : RexPrefix rex.toBitVec) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => SseAlignedLoadPre p
        (fun t => base + am.addr t (p + BitVec.ofNat 64 (5 + am.tail.length))) s ∧ r.Ready base s)
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0x57 :: am.modrm reg :: am.tail))
      (Effect.post (xorpsXmmM128SegEffect p (5 + am.tail.length) base
        (gprNumber 0 (rexR rex.toBitVec) reg) am)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
    (xorps_xmm_m128_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

/-- The triple for `xorps dst, r:[am]` on the XMM register numbered `dst` (0–15) at `p`, in the
encoding `r.prefixByte :: encodeXorpsXmmM128 dst am`. -/
theorem xorps_xmm_m128_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (dst : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => SseAlignedLoadPre p (fun t => base + am.addr t
        (p + BitVec.ofNat 64 (r.prefixByte :: encodeXorpsXmmM128 dst am).length)) s ∧
        r.Ready base s)
      (codeRange p (r.prefixByte :: encodeXorpsXmmM128 dst am))
      (Effect.post (xorpsXmmM128SegEffect p (r.prefixByte :: encodeXorpsXmmM128 dst am).length
        base (dst.setWidth 5) am)) := by
  unfold encodeXorpsXmmM128
  rcases encodeSseMem_spec 0x57 dst am with ⟨hbytes, hx, hb, hreg⟩ | hbytes
  · have hl : (r.prefixByte :: 0x0F :: 0x57 :: am.modrm (regLow dst) :: am.tail :
        List UInt8).length = 4 + am.tail.length := by simp; omega
    rw [hbytes, ← hreg, hl]
    exact xorps_xmm_m128_seg_triple_of_bytes p r base (regLow dst) am hv hx hb
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec dst
    have := xorps_xmm_m128_rex_seg_triple_of_bytes p r base _ hrex.rexPrefix (regLow dst) am hv
      hx hb
    rw [hr, gprNumber_reg] at this
    have hl : (r.prefixByte :: am.rexByte false dst :: 0x0F :: 0x57 :: am.modrm (regLow dst) ::
        am.tail).length = 5 + am.tail.length := by simp; omega
    rw [hbytes, hl]
    exact this

/-! ### Examples -/

/-- `0F 57 44 24 10`: `xorps xmm0, [rsp + 0x10]`. -/
example [Bindings] (p : BitVec 64) :
    Triple (SseAlignedLoadPre p (fun s => (AddrMode.sib 4 none 0 (.d8 0x10)).addr s (p + 5)))
      (codeRange p [0x0F, 0x57, 0x44, 0x24, 0x10])
      (Effect.post (xorpsXmmM128Effect p 5 0 (.sib 4 none 0 (.d8 0x10)))) :=
  xorps_xmm_m128_triple_of_bytes p 0 (.sib 4 none 0 (.d8 0x10)) ⟨by decide, fun _ => by decide⟩
    rfl rfl

/-- `0F 57 8C 24 80 00 00 00`: `xorps xmm1, [rsp + 0x80]`. -/
example [Bindings] (p : BitVec 64) :
    Triple (SseAlignedLoadPre p (fun s => (AddrMode.sib 4 none 0 (.d32 0x80)).addr s (p + 8)))
      (codeRange p [0x0F, 0x57, 0x8C, 0x24, 0x80, 0x00, 0x00, 0x00])
      (Effect.post (xorpsXmmM128Effect p 8 1 (.sib 4 none 0 (.d32 0x80)))) :=
  xorps_xmm_m128_triple_of_bytes p 1 (.sib 4 none 0 (.d32 0x80)) ⟨by decide, fun _ => by decide⟩
    rfl rfl

/-- `0F 57 44 0C 10`: `xorps xmm0, [rsp + rcx + 0x10]`. -/
example [Bindings] (p : BitVec 64) :
    Triple (SseAlignedLoadPre p (fun s => (AddrMode.sib 4 (some 1) 0 (.d8 0x10)).addr s (p + 5)))
      (codeRange p [0x0F, 0x57, 0x44, 0x0C, 0x10])
      (Effect.post (xorpsXmmM128Effect p 5 0 (.sib 4 (some 1) 0 (.d8 0x10)))) :=
  xorps_xmm_m128_triple_of_bytes p 0 (.sib 4 (some 1) 0 (.d8 0x10))
    ⟨by decide, fun _ => by decide⟩ rfl rfl

/-- `encodeXorpsXmmM128` gives the expected bytes. -/
example : encodeXorpsXmmM128 0 (.sib 4 none 0 (.d8 0x10)) = [0x0F, 0x57, 0x44, 0x24, 0x10] := by decide
example : encodeXorpsXmmM128 1 (.sib 4 none 0 (.d8 0x20)) = [0x0F, 0x57, 0x4C, 0x24, 0x20] := by decide
example : encodeXorpsXmmM128 0 (.sib 4 none 0 (.d32 0x90)) =
    [0x0F, 0x57, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00] := by decide
example : encodeXorpsXmmM128 1 (.sib 4 (some 1) 0 (.d8 0x20)) = [0x0F, 0x57, 0x4C, 0x0C, 0x20] := by
  decide

/-- A REX encoding, `44 0F 57 4C 24 20`: `xorps xmm9, [rsp + 0x20]`. -/
example : encodeXorpsXmmM128 9 (.sib 4 none 0 (.d8 0x20)) = [0x44, 0x0F, 0x57, 0x4C, 0x24, 0x20] := by
  decide
attribute [x86_compose] xorpsXmmM128Effect

@[x86_local] theorem xorpsXmmM128Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {am : AddrMode} :
    Effect.Local (xorpsXmmM128Effect p len dst am) := by
  effect_local [xorpsXmmM128Effect]

attribute [x86_compose] xorpsXmmM128SegEffect

@[x86_local] theorem xorpsXmmM128SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {dst : BitVec 5} {am : AddrMode} :
    Effect.Local (xorpsXmmM128SegEffect p len base dst am) := by
  effect_local [xorpsXmmM128SegEffect]

end X86Proofs
