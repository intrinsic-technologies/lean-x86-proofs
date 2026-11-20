import X86Proofs.Instructions.Movzx.Generated.RR16.Step
import X86Proofs.Instructions.Movzx.Generated.RR16.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movzxR32R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (x).setWidth 64⟩] }

@[simp] theorem movzxR32R16Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (movzxR32R16Effect p len dst src s).components = [.reg dst, .rip] := rfl

def movzxR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 ((x).setWidth 16) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movzxR16R16Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (movzxR16R16Effect p len dst src s).components = [.reg dst, .rip] := rfl

theorem movzx_r64_r16_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xB7, modrm]))
      (movzxR32R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movzx_r_r16_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movzxSpec]

theorem movzx_r64_r16_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xB7, modrm]))
      (Effect.post (movzxR32R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movzxR32R16Effect_components]; simp [Component.Covers]) _)
    (movzx_r64_r16_effect_step p rex hrex modrm hmod)

theorem movzx_r32_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xB7, modrm]))
      (movzxR32R16Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movzx_r_r16_step s h [] (by simp)
    (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec]
  exact BitVec.setWidth_setWidth (by decide)

theorem movzx_r32_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xB7, modrm]))
      (Effect.post (movzxR32R16Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movzxR32R16Effect_components]; simp [Component.Covers]) _)
    (movzx_r32_r16_effect_step p modrm hmod)

theorem movzx_r32_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xB7, modrm]))
      (movzxR32R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movzx_r_r16_step s h [rex] (by simpa using hr.scanPrefix)
    (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movzxSpec]
  exact BitVec.setWidth_setWidth (by decide)

theorem movzx_r32_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xB7, modrm]))
      (Effect.post (movzxR32R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movzxR32R16Effect_components]; simp [Component.Covers]) _)
    (movzx_r32_r16_rex_effect_step p rex hrex modrm hmod)

theorem movzx_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x0F, 0xB7, modrm]))
      (movzxR16R16Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movzx_r16_r16_step s h [0x66] (by simpa using scanPrefix_66)
    (by simp)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movzxSpec]

theorem movzx_r16_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x0F, 0xB7, modrm]))
      (Effect.post (movzxR16R16Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movzxR16R16Effect_components]; simp [Component.Covers]) _)
    (movzx_r16_r16_effect_step p modrm hmod)

theorem movzx_r16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x66, rex, 0x0F, 0xB7, modrm]))
      (movzxR16R16Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movzx_r16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
    (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, movzxSpec]

theorem movzx_r16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x66, rex, 0x0F, 0xB7, modrm]))
      (Effect.post (movzxR16R16Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movzxR16R16Effect_components]; simp [Component.Covers]) _)
    (movzx_r16_r16_rex_effect_step p rex hrex modrm hmod)

theorem movzx_r64_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovzxR64R16 dst src))
      (Effect.post (movzxR32R16Effect p (encodeMovzxR64R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeMovzxR64R16_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact movzx_r64_r16_triple_of_bytes p rex hrex modrm hmod

theorem movzx_r32_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovzxR32R16 dst src))
      (Effect.post (movzxR32R16Effect p (encodeMovzxR32R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeMovzxR32R16_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact movzx_r32_r16_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact movzx_r32_r16_rex_triple_of_bytes p rex hrex modrm hmod

theorem movzx_r16_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovzxR16R16 dst src))
      (Effect.post (movzxR16R16Effect p (encodeMovzxR16R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeMovzxR16R16_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact movzx_r16_r16_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact movzx_r16_r16_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] movzxR32R16Effect movzxR16R16Effect

@[x86_local] theorem movzxR32R16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (movzxR32R16Effect p len dst src) := by
  effect_local [movzxR32R16Effect]

@[x86_local] theorem movzxR16R16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (movzxR16R16Effect p len dst src) := by
  effect_local [movzxR16R16Effect]

end X86Proofs
