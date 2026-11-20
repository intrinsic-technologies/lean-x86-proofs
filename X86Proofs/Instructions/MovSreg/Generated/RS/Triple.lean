import X86Proofs.Instructions.MovSreg.Generated.RS.Step
import X86Proofs.Instructions.MovSreg.Generated.RS.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movRSregEffect (p : BitVec 64) (len n : Nat) (dst : BitVec 5) (sel : BitVec 16)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR n (movsregSpec n sel) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem movRSregEffect_components (p : BitVec 64) (len n : Nat) (dst : BitVec 5)
    (sel : BitVec 16) (s : RamState) :
    (movRSregEffect p len n dst sel s).components = [.reg dst, .rip] := rfl

theorem mov_r64_sreg_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [rex, 0x8C, modrm])
      (movRSregEffect p 3 64 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) sel) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hsel⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := mov_r_sreg_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (by decide)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod hsreg hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4 (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsel] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem mov_r64_sreg_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [rex, 0x8C, modrm])
      (Effect.post (movRSregEffect p 3 64 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) sel)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movRSregEffect_components]; simp [Component.Covers]) _)
    (mov_r64_sreg_effect_step p rex hrex modrm hmod hsreg sel)

theorem mov_r32_sreg_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [0x8C, modrm])
      (movRSregEffect p 2 32 (gprNumber 0 0 (modrmRm modrm)) sel) := by
  rintro s h hcode ⟨hp, hsel⟩
  subst hp
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := mov_r_sreg_step s h [] (by simp) (by simp) 32 (by decide)
    (by exact rfl) (by rfl) (by rfl) modrm hmod hsreg hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsel] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem mov_r32_sreg_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [0x8C, modrm])
      (Effect.post (movRSregEffect p 2 32 (gprNumber 0 0 (modrmRm modrm)) sel)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movRSregEffect_components]; simp [Component.Covers]) _)
    (mov_r32_sreg_effect_step p modrm hmod hsreg sel)

theorem mov_r32_sreg_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [rex, 0x8C, modrm])
      (movRSregEffect p 3 32 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) sel) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hsel⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := mov_r_sreg_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (by decide)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) modrm hmod hsreg hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4 (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsel] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem mov_r32_sreg_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [rex, 0x8C, modrm])
      (Effect.post (movRSregEffect p 3 32 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) sel)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movRSregEffect_components]; simp [Component.Covers]) _)
    (mov_r32_sreg_rex_effect_step p rex hrex modrm hmod hsreg sel)

theorem mov_r16_sreg_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [0x66, 0x8C, modrm])
      (movRSregEffect p 3 16 (gprNumber 0 0 (modrmRm modrm)) sel) := by
  rintro s h hcode ⟨hp, hsel⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := mov_r_sreg_step s h [0x66] (by simpa using scanPrefix_66) (by simp) 16 (by decide)
    (by exact rfl) (by rfl) (by rfl) modrm hmod hsreg hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsel] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem mov_r16_sreg_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [0x66, 0x8C, modrm])
      (Effect.post (movRSregEffect p 3 16 (gprNumber 0 0 (modrmRm modrm)) sel)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movRSregEffect_components]; simp [Component.Covers]) _)
    (mov_r16_sreg_effect_step p modrm hmod hsreg sel)

theorem mov_r16_sreg_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [0x66, rex, 0x8C, modrm])
      (movRSregEffect p 4 16 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) sel) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hsel⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := mov_r_sreg_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp) 16 (by decide)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS) (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) modrm hmod hsreg hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4 (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsel] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem mov_r16_sreg_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hsreg : (modrmReg modrm).toNat < 6) (sel : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ segSelector s (modrmReg modrm) = sel)
      (codeRange p [0x66, rex, 0x8C, modrm])
      (Effect.post (movRSregEffect p 4 16 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) sel)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movRSregEffect_components]; simp [Component.Covers]) _)
    (mov_r16_sreg_rex_effect_step p rex hrex modrm hmod hsreg sel)

theorem mov_r64_sreg_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (sreg : BitVec 3)
    (hs : sreg.toNat < 6) (sel : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ segSelector s sreg = sel)
      (codeRange p (encodeMovR64Sreg dst sreg))
      (Effect.post (movRSregEffect p 3 64 (dst.setWidth 5) sel)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeMovR64Sreg_spec dst sreg
  subst hreg
  rw [hbytes, ← hdst]
  exact mov_r64_sreg_triple_of_bytes p rex hrex modrm hmod hs sel

theorem mov_r32_sreg_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (sreg : BitVec 3)
    (hs : sreg.toNat < 6) (sel : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ segSelector s sreg = sel)
      (codeRange p (encodeMovR32Sreg dst sreg))
      (Effect.post (movRSregEffect p (encodeMovR32Sreg dst sreg).length 32 (dst.setWidth 5)
        sel)) := by
  rcases encodeMovR32Sreg_spec dst sreg with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · subst hreg
    rw [hbytes, ← hdst]
    exact mov_r32_sreg_triple_of_bytes p modrm hmod hs sel
  · subst hreg
    rw [hbytes, ← hdst]
    exact mov_r32_sreg_rex_triple_of_bytes p rex hrex modrm hmod hs sel

theorem mov_r16_sreg_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (sreg : BitVec 3)
    (hs : sreg.toNat < 6) (sel : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ segSelector s sreg = sel)
      (codeRange p (encodeMovR16Sreg dst sreg))
      (Effect.post (movRSregEffect p (encodeMovR16Sreg dst sreg).length 16 (dst.setWidth 5)
        sel)) := by
  rcases encodeMovR16Sreg_spec dst sreg with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · subst hreg
    rw [hbytes, ← hdst]
    exact mov_r16_sreg_triple_of_bytes p modrm hmod hs sel
  · subst hreg
    rw [hbytes, ← hdst]
    exact mov_r16_sreg_rex_triple_of_bytes p rex hrex modrm hmod hs sel

attribute [x86_compose] movRSregEffect

@[x86_local] theorem movRSregEffect_local {p : BitVec 64} {len n : Nat} {dst : BitVec 5}
    {sel : BitVec 16} :
    Effect.Local (movRSregEffect p len n dst sel) := by
  effect_local [movRSregEffect]

end X86Proofs
