import X86Proofs.Instructions.Cmp.Generated.Imm32.Step
import X86Proofs.Instructions.Cmp.Generated.Imm32.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def cmpR64Imm32Effect (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := imm.signExtend 64
  { rip := p + 7
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR64Imm32Effect_components (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32)
    (s : RamState) :
    (cmpR64Imm32Effect p dst imm s).components = [.flags, .rip] := rfl

theorem cmpR64Imm32Effect_avoids (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (cmpR64Imm32Effect p dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem cmp_r64_imm32_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (cmpR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_r64_imm32_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_r64_imm32_ready h rex modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 7 _ 0 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 7 _ 0 _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r64_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (Effect.post (cmpR64Imm32Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => cmpR64Imm32Effect_avoids p _ _ s _)
    (cmp_r64_imm32_effect_step p rex modrm imm hrex hmod hreg)

theorem cmp_r64_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeCmpR64Imm32 dst imm))
      (Effect.post (cmpR64Imm32Effect p (dst.setWidth 5) imm)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeCmpR64Imm32_spec dst imm
  rw [hbytes, ← hdst]
  exact cmp_r64_imm32_triple_of_bytes p rex modrm imm hrex hmod hreg

def cmpR32Imm32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := imm.signExtend 32
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR32Imm32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32)
    (s : RamState) :
    (cmpR32Imm32Effect p len dst imm s).components = [.flags, .rip] := rfl

theorem cmpR32Imm32Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (s : RamState)
    (code : CodeMap) : (cmpR32Imm32Effect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem cmp_r32_imm32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 32) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x81 :: modrm :: immBytes 32 imm))
      (cmpR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_r32_imm32_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_r32_imm32_ready h modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 6 _ 0 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 6 _ 0 _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r32_imm32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 32) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p (0x81 :: modrm :: immBytes 32 imm))
      (Effect.post (cmpR32Imm32Effect p 6 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => cmpR32Imm32Effect_avoids p _ _ _ s _)
    (cmp_r32_imm32_effect_step p modrm imm hmod hreg)

theorem cmp_r32_imm32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (cmpR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_r32_imm32_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_r32_imm32_rex_ready h rex modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 7 _ 0 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 7 _ 0 _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r32_imm32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 32) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p (rex :: 0x81 :: modrm :: immBytes 32 imm))
      (Effect.post (cmpR32Imm32Effect p 7 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => cmpR32Imm32Effect_avoids p _ _ _ s _)
    (cmp_r32_imm32_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem cmp_r32_imm32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 32) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeCmpR32Imm32 dst imm))
      (Effect.post (cmpR32Imm32Effect p (encodeCmpR32Imm32 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeCmpR32Imm32_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using cmp_r32_imm32_triple_of_bytes p modrm imm hmod hreg
  · rw [hbytes, ← hdst]
    simpa using cmp_r32_imm32_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

def cmpR16Imm16Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := imm.signExtend 16
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (.ofStatusFlags (cmpSpec a b)) }

@[simp] theorem cmpR16Imm16Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16)
    (s : RamState) :
    (cmpR16Imm16Effect p len dst imm s).components = [.flags, .rip] := rfl

theorem cmpR16Imm16Effect_avoids (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (s : RamState)
    (code : CodeMap) : (cmpR16Imm16Effect p len dst imm s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem cmp_r16_imm16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 16) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: 0x81 :: modrm :: immBytes 16 imm))
      (cmpR16Imm16Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_r16_imm16_step s h modrm imm hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_r16_imm16_ready h modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 5 _ 0 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 5 _ 0 _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r16_imm16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (imm : BitVec 16) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: 0x81 :: modrm :: immBytes 16 imm))
      (Effect.post (cmpR16Imm16Effect p 5 (gprNumber 0 0 (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => cmpR16Imm16Effect_avoids p _ _ _ s _)
    (cmp_r16_imm16_effect_step p modrm imm hmod hreg)

theorem cmp_r16_imm16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 16) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    StepEffect (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0x81 :: modrm :: immBytes 16 imm))
      (cmpR16Imm16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm) := by
  rintro s h hcode rfl
  refine ⟨_, cmp_r16_imm16_rex_step s h rex modrm imm hrex hmod hreg hcode.bytesAt
    (by simpa using hcode.low (by simp) (by simp)), cmp_r16_imm16_rex_ready h rex modrm imm,
    ⟨afterStep_writeFlagsOutputs_rip h 6 _ 0 _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s 6 _ 0 _⟩⟩
  · exact StatusFlagsOutcome.allows_ofStatusFlags _

theorem cmp_r16_imm16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (imm : BitVec 16) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    Triple (fun s => s.RIP = p) (codeRange p (0x66 :: rex :: 0x81 :: modrm :: immBytes 16 imm))
      (Effect.post (cmpR16Imm16Effect p 6 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm)) :=
  Triple.of_effect (fun s _ => cmpR16Imm16Effect_avoids p _ _ _ s _)
    (cmp_r16_imm16_rex_effect_step p rex modrm imm hrex hmod hreg)

theorem cmp_r16_imm16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (imm : BitVec 16) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeCmpR16Imm16 dst imm))
      (Effect.post (cmpR16Imm16Effect p (encodeCmpR16Imm16 dst imm).length (dst.setWidth 5) imm)) := by
  rcases encodeCmpR16Imm16_spec dst imm with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    simpa using cmp_r16_imm16_triple_of_bytes p modrm imm hmod hreg
  · rw [hbytes, ← hdst]
    simpa using cmp_r16_imm16_rex_triple_of_bytes p rex modrm imm hrex hmod hreg

attribute [x86_compose] cmpR64Imm32Effect cmpR32Imm32Effect cmpR16Imm16Effect

@[x86_local] theorem cmpR64Imm32Effect_local {p : BitVec 64} {dst : BitVec 5} {imm32 : BitVec 32} :
    Effect.Local (cmpR64Imm32Effect p dst imm32) := by
  effect_local [cmpR64Imm32Effect]

@[x86_local] theorem cmpR32Imm32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm32 : BitVec 32} :
    Effect.Local (cmpR32Imm32Effect p len dst imm32) := by
  effect_local [cmpR32Imm32Effect]

@[x86_local] theorem cmpR16Imm16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {imm16 : BitVec 16} :
    Effect.Local (cmpR16Imm16Effect p len dst imm16) := by
  effect_local [cmpR16Imm16Effect]

end X86Proofs
