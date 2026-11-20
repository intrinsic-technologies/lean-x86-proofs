import X86Proofs.Instructions.Xorps.Step
import X86Proofs.Instructions.Xorps.Encode
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

/-!
# XORPS triples

`xorps xmm, xmm` (`0F 57 /r`, `mod = 3`): the destination XMM register (`reg`) becomes its old
value xor the source (`rm`), 128 bits; bits 128–511 of its ZMM register are kept (they are not
part of the `.xmm` component, so `AgreesExcept` keeps them); no flags. The precondition is
`SsePre p` (RIP = `p` and SSE enabled), the effect `xorpsXmmXmmEffect`.

- `xorps_xmm_xmm_triple_of_bytes`: `0F 57 modrm`, registers 0–7.
- `xorps_xmm_xmm_rex_triple_of_bytes`: `rex 0F 57 modrm`, any of the 16 registers.
- `xorps_xmm_xmm_triple`: registers given by number (0–15), in the encoding `encodeXorpsXmmXmm`.
- Examples on the encoding `0F 57 C0` (`xorps xmm0, xmm0`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The effect of `xorps dst, src` at `p`, for an encoding of `len` bytes (3 without a REX prefix,
4 with one), from state `s`: RIP = `p + len`, the XMM register `dst` set to the old `dst` xor the
old `src` (128 bits). No flags. -/
def xorpsXmmXmmEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.xmm dst : Operand 128),
    (Operand.xmm dst : Operand 128).read s ^^^ (Operand.xmm src : Operand 128).read s⟩]

/-- XORPS changes the destination XMM register and RIP. -/
@[simp] theorem xorpsXmmXmmEffect_components (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : (xorpsXmmXmmEffect p len dst src s).components = [.xmm dst, .rip] := rfl

/-- XORPS writes no memory. -/
theorem xorpsXmmXmmEffect_avoids (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState)
    (code : CodeMap) : (xorpsXmmXmmEffect p len dst src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

/-- The step behind `xorps_xmm_xmm_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `xorpsXmmXmmEffect`. -/
theorem xorps_xmm_xmm_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (SsePre p) (codeRange p [0x0F, 0x57, modrm])
      (xorpsXmmXmmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hsse⟩
  refine ⟨_, xorps_xmm_xmm_step s h hsse modrm hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult_xmm h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

/--
The triple for `xorps xmm, xmm` (`0F 57 /r`, no prefix, `mod = 3`) at address `p`, for any ModRM
byte: the effect `xorpsXmmXmmEffect` on the destination (`reg`) and the source (`rm`).
-/
theorem xorps_xmm_xmm_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (SsePre p) (codeRange p [0x0F, 0x57, modrm])
      (Effect.post (xorpsXmmXmmEffect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => xorpsXmmXmmEffect_avoids p _ _ _ s _)
    (xorps_xmm_xmm_effect_step p modrm hmod)

/-- The step behind `xorps_xmm_xmm_rex_triple_of_bytes`: from a ready state with the instruction in
memory and the precondition, one `step` reaches a ready state with the effect `xorpsXmmXmmEffect`. -/
theorem xorps_xmm_xmm_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    StepEffect (SsePre p) (codeRange p [rex, 0x0F, 0x57, modrm])
      (xorpsXmmXmmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hsse⟩
  refine ⟨_, xorps_xmm_xmm_rex_step s h hsse rex modrm hrex hmod hcode.bytesAt
    (hcode.low (by simp) (by simp)), ReadyToStep.afterStep_writeResult_xmm h 4 _ _ _,
    ⟨afterStep_writeResult_rip h 4 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult_xmm s 4 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep_writeResult_xmm]
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch]

/--
The triple for `xorps xmm, xmm` after a REX prefix (`rex 0F 57 /r`, `mod = 3`) at address `p`:
the effect `xorpsXmmXmmEffect` on the destination (`reg` extended by REX.R) and the source (`rm`
extended by REX.B).
-/
theorem xorps_xmm_xmm_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) :
    Triple (SsePre p) (codeRange p [rex, 0x0F, 0x57, modrm])
      (Effect.post (xorpsXmmXmmEffect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => xorpsXmmXmmEffect_avoids p _ _ _ s _)
    (xorps_xmm_xmm_rex_effect_step p rex modrm hrex hmod)

/--
The triple for `xorps dst, src` on XMM registers numbered `dst` and `src` (0–15) at address `p`,
in the encoding `encodeXorpsXmmXmm`: the effect `xorpsXmmXmmEffect` on those registers, with the length of
that encoding (3 or 4).
-/
theorem xorps_xmm_xmm_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (SsePre p) (codeRange p (encodeXorpsXmmXmm dst src))
      (Effect.post (xorpsXmmXmmEffect p (encodeXorpsXmmXmm dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeXorpsXmmXmm_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact xorps_xmm_xmm_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact xorps_xmm_xmm_rex_triple_of_bytes p rex modrm hrex hmod

/-! ### Examples -/

/-- `0F 57 C0` is `xorps xmm0, xmm0`: it sets XMM0 to 0 (`x ^^^ x`). -/
example [Bindings] (p : BitVec 64) :
    Triple (SsePre p) (codeRange p [0x0F, 0x57, 0xC0]) (Effect.post (xorpsXmmXmmEffect p 3 0 0)) :=
  xorps_xmm_xmm_triple_of_bytes p 0xC0 (by decide)

/-- `encodeXorpsXmmXmm 0 0` is `0F 57 C0`. -/
example : encodeXorpsXmmXmm 0 0 = [0x0F, 0x57, 0xC0] := by decide

/-- `xorps xmm0, xmm0` zeroes XMM0: the written value is 0 whatever XMM0 held. -/
example (p : BitVec 64) (s : RamState) :
    (xorpsXmmXmmEffect p 3 0 0 s).writes = [⟨(Operand.xmm 0 : Operand 128), 0⟩] := by
  simp [xorpsXmmXmmEffect]

/-- A REX encoding, `44 0F 57 C9`: `xorps xmm9, xmm1`. -/
example [Bindings] (p : BitVec 64) :
    Triple (SsePre p) (codeRange p [0x44, 0x0F, 0x57, 0xC9]) (Effect.post (xorpsXmmXmmEffect p 4 9 1)) :=
  xorps_xmm_xmm_rex_triple_of_bytes p 0x44 0xC9 (by unfold RexPrefix; decide) (by decide)
attribute [x86_compose] xorpsXmmXmmEffect

@[x86_local] theorem xorpsXmmXmmEffect_local {p : BitVec 64} {len : Nat} {dst src : BitVec 5} :
    Effect.Local (xorpsXmmXmmEffect p len dst src) := by
  effect_local [xorpsXmmXmmEffect]

end X86Proofs
