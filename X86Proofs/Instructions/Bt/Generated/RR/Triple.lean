import X86Proofs.Instructions.Bt.Generated.RR.Step
import X86Proofs.Instructions.Bt.Generated.RR.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def btR64R64Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btR64R64Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (btR64R64Effect p len dst src s).components =
      [.flags, .rip] := rfl

def btR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btR32R32Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (btR32R32Effect p len dst src s).components =
      [.flags, .rip] := rfl

def btR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let a := (Operand.reg dst : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := []
    flags := some (btFlags (StatusFlags.ofRFLAGS s.RFLAGS) a b) }

@[simp] theorem btR16R16Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (btR16R16Effect p len dst src s).components =
      [.flags, .rip] := rfl

theorem bt_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xA3, modrm]))
      (btR64R64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := bt_r_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xA3, modrm]))
      (Effect.post (btR64R64Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR64R64Effect_components]; simp [Component.Covers]) _)
    (bt_r64_r64_effect_step p rex hrex modrm hmod)

theorem bt_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xA3, modrm]))
      (btR32R32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := bt_r_r_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xA3, modrm]))
      (Effect.post (btR32R32Effect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR32R32Effect_components]; simp [Component.Covers]) _)
    (bt_r32_r32_effect_step p modrm hmod)

theorem bt_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xA3, modrm]))
      (btR32R32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := bt_r_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4
      (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xA3, modrm]))
      (Effect.post (btR32R32Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR32R32Effect_components]; simp [Component.Covers]) _)
    (bt_r32_r32_rex_effect_step p rex hrex modrm hmod)

theorem bt_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x0F, 0xA3, modrm]))
      (btR16R16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := bt_r16_r16_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl) modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r16_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x66, 0x0F, 0xA3, modrm]))
      (Effect.post (btR16R16Effect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR16R16Effect_components]; simp [Component.Covers]) _)
    (bt_r16_r16_effect_step p modrm hmod)

theorem bt_r16_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x66, rex, 0x0F, 0xA3, modrm]))
      (btR16R16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := bt_r16_r16_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4
      (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeFlagsOutputs h _ _ _ _,
    ⟨afterStep_writeFlagsOutputs_rip h _ _ _ _, trivial, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeFlagsOutputs s _ _ _ _⟩⟩
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
    beforeFetch_RFLAGS]
  exact btFlags_allows _ _ _ _

theorem bt_r16_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x66, rex, 0x0F, 0xA3, modrm]))
      (Effect.post (btR16R16Effect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [btR16R16Effect_components]; simp [Component.Covers]) _)
    (bt_r16_r16_rex_effect_step p rex hrex modrm hmod)

theorem bt_r64_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBtR64R64 dst src))
      (Effect.post (btR64R64Effect p (encodeBtR64R64 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeBtR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact bt_r64_r64_triple_of_bytes p rex hrex modrm hmod

theorem bt_r32_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBtR32R32 dst src))
      (Effect.post (btR32R32Effect p (encodeBtR32R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeBtR32R32_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact bt_r32_r32_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact bt_r32_r32_rex_triple_of_bytes p rex hrex modrm hmod

theorem bt_r16_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBtR16R16 dst src))
      (Effect.post (btR16R16Effect p (encodeBtR16R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeBtR16R16_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact bt_r16_r16_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact bt_r16_r16_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] btR64R64Effect btR32R32Effect btR16R16Effect

@[x86_local] theorem btR64R64Effect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} :
    Effect.Local (btR64R64Effect p len dst src) := by
  effect_local [btR64R64Effect, btFlags]

@[x86_local] theorem btR32R32Effect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} :
    Effect.Local (btR32R32Effect p len dst src) := by
  effect_local [btR32R32Effect, btFlags]

@[x86_local] theorem btR16R16Effect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} :
    Effect.Local (btR16R16Effect p len dst src) := by
  effect_local [btR16R16Effect, btFlags]

end X86Proofs
