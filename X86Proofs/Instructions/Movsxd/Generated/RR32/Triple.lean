import X86Proofs.Instructions.Movsxd.Generated.RR32.Step
import X86Proofs.Instructions.Movsxd.Generated.RR32.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movsxdR64R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (x).signExtend 64⟩] }

@[simp] theorem movsxdR64R32Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (movsxdR64R32Effect p len dst src s).components = [.reg dst, .rip] := rfl

def movsxdR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      ((x).signExtend 32).setWidth 64⟩] }

@[simp] theorem movsxdR32R32Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (movsxdR32R32Effect p len dst src s).components = [.reg dst, .rip] := rfl

def movsxdR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 ((x).signExtend 16) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movsxdR16R16Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (movsxdR16R16Effect p len dst src s).components = [.reg dst, .rip] := rfl

theorem movsxd_r64_r32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x63, modrm]))
      (movsxdR64R32Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsxd_r_r32_step s h [rex] (by simpa using hr.scanPrefix)
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
  simp only [Operand.read_writeResult_self, movsxdSpec]

theorem movsxd_r64_r32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x63, modrm]))
      (Effect.post (movsxdR64R32Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxdR64R32Effect_components]; simp [Component.Covers]) _)
    (movsxd_r64_r32_effect_step p rex hrex modrm hmod)

theorem movsxd_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x63, modrm]))
      (movsxdR32R32Effect p 2 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsxd_r_r32_step s h [] (by simp)
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
  simp only [Operand.read_writeResult_self32, movsxdSpec]

theorem movsxd_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x63, modrm]))
      (Effect.post (movsxdR32R32Effect p 2 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxdR32R32Effect_components]; simp [Component.Covers]) _)
    (movsxd_r32_r32_effect_step p modrm hmod)

theorem movsxd_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x63, modrm]))
      (movsxdR32R32Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsxd_r_r32_step s h [rex] (by simpa using hr.scanPrefix)
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
  simp only [Operand.read_writeResult_self32, movsxdSpec]

theorem movsxd_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x63, modrm]))
      (Effect.post (movsxdR32R32Effect p 3 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxdR32R32Effect_components]; simp [Component.Covers]) _)
    (movsxd_r32_r32_rex_effect_step p rex hrex modrm hmod)

theorem movsxd_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x63, modrm]))
      (movsxdR16R16Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsxd_r16_r16_step s h [0x66] (by simpa using scanPrefix_66)
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
    Operand.read_beforeFetch, movsxdSpec]

theorem movsxd_r16_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x63, modrm]))
      (Effect.post (movsxdR16R16Effect p 3 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxdR16R16Effect_components]; simp [Component.Covers]) _)
    (movsxd_r16_r16_effect_step p modrm hmod)

theorem movsxd_r16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x66, rex, 0x63, modrm]))
      (movsxdR16R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := movsxd_r16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix])
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
    Operand.read_beforeFetch, movsxdSpec]

theorem movsxd_r16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x66, rex, 0x63, modrm]))
      (Effect.post (movsxdR16R16Effect p 4 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movsxdR16R16Effect_components]; simp [Component.Covers]) _)
    (movsxd_r16_r16_rex_effect_step p rex hrex modrm hmod)

theorem movsxd_r64_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovsxdR64R32 dst src))
      (Effect.post (movsxdR64R32Effect p (encodeMovsxdR64R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeMovsxdR64R32_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact movsxd_r64_r32_triple_of_bytes p rex hrex modrm hmod

theorem movsxd_r32_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovsxdR32R32 dst src))
      (Effect.post (movsxdR32R32Effect p (encodeMovsxdR32R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeMovsxdR32R32_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact movsxd_r32_r32_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact movsxd_r32_r32_rex_triple_of_bytes p rex hrex modrm hmod

theorem movsxd_r16_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeMovsxdR16R16 dst src))
      (Effect.post (movsxdR16R16Effect p (encodeMovsxdR16R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeMovsxdR16R16_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact movsxd_r16_r16_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact movsxd_r16_r16_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] movsxdR64R32Effect movsxdR32R32Effect movsxdR16R16Effect

@[x86_local] theorem movsxdR64R32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (movsxdR64R32Effect p len dst src) := by
  effect_local [movsxdR64R32Effect]

@[x86_local] theorem movsxdR32R32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (movsxdR32R32Effect p len dst src) := by
  effect_local [movsxdR32R32Effect]

@[x86_local] theorem movsxdR16R16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (movsxdR16R16Effect p len dst src) := by
  effect_local [movsxdR16R16Effect]

end X86Proofs
