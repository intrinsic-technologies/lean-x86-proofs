import X86Proofs.Instructions.Sldt.Generated.R.Step
import X86Proofs.Instructions.Sldt.Generated.R.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def sldtREffect (p : BitVec 64) (len n : Nat) (dst : BitVec 5) (v : BitVec 16)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR n (sldtSpec n v) ((Operand.reg dst : Operand 64).read s)⟩] }

@[simp] theorem sldtREffect_components (p : BitVec 64) (len n : Nat) (dst : BitVec 5)
    (v : BitVec 16) (s : RamState) :
    (sldtREffect p len n dst v s).components = [.reg dst, .rip] := rfl

theorem sldt_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [rex, 0x0F, 0x00, modrm])
      (sldtREffect p 4 64 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) v) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hsys, hval⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := sldt_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (by decide)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) hsys modrm hmod hreg hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4 (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hval] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem sldt_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [rex, 0x0F, 0x00, modrm])
      (Effect.post (sldtREffect p 4 64 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) v)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [sldtREffect_components]; simp [Component.Covers]) _)
    (sldt_r64_effect_step p rex hrex modrm hmod hreg v)

theorem sldt_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [0x0F, 0x00, modrm])
      (sldtREffect p 3 32 (gprNumber 0 0 (modrmRm modrm)) v) := by
  rintro s h hcode ⟨hp, hsys, hval⟩
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := sldt_r_step s h [] (by simp) (by simp) 32 (by decide)
    (by exact rfl) (by rfl) (by rfl) hsys modrm hmod hreg hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) []).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hval] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem sldt_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [0x0F, 0x00, modrm])
      (Effect.post (sldtREffect p 3 32 (gprNumber 0 0 (modrmRm modrm)) v)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [sldtREffect_components]; simp [Component.Covers]) _)
    (sldt_r32_effect_step p modrm hmod hreg v)

theorem sldt_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [rex, 0x0F, 0x00, modrm])
      (sldtREffect p 4 32 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) v) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hsys, hval⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := sldt_r_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (by decide)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) hsys modrm hmod hreg hcode.bytesAt hlow
  simp only [scanContext_rex _ _ hr] at hstep
  have hdst : gprNumber (rexContext s.DS rex.toBitVec).rex_b4 (rexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hval] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem sldt_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [rex, 0x0F, 0x00, modrm])
      (Effect.post (sldtREffect p 4 32 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) v)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [sldtREffect_components]; simp [Component.Covers]) _)
    (sldt_r32_rex_effect_step p rex hrex modrm hmod hreg v)

theorem sldt_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [0x66, 0x0F, 0x00, modrm])
      (sldtREffect p 4 16 (gprNumber 0 0 (modrmRm modrm)) v) := by
  rintro s h hcode ⟨hp, hsys, hval⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := sldt_r_step s h [0x66] (by simpa using scanPrefix_66) (by simp) 16 (by decide)
    (by exact rfl) (by rfl) (by rfl) hsys modrm hmod hreg hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hval] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem sldt_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [0x66, 0x0F, 0x00, modrm])
      (Effect.post (sldtREffect p 4 16 (gprNumber 0 0 (modrmRm modrm)) v)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [sldtREffect_components]; simp [Component.Covers]) _)
    (sldt_r16_effect_step p modrm hmod hreg v)

theorem sldt_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    StepEffect (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [0x66, rex, 0x0F, 0x00, modrm])
      (sldtREffect p 5 16 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) v) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hsys, hval⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := sldt_r_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp) 16 (by decide)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS) (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl) hsys modrm hmod hreg hcode.bytesAt hlow
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hdst : gprNumber (oszRexContext s.DS rex.toBitVec).rex_b4 (oszRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hval] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeResult h _ _ _ _,
    ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep, Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem sldt_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0) (v : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p [0x66, rex, 0x0F, 0x00, modrm])
      (Effect.post (sldtREffect p 5 16 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) v)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [sldtREffect_components]; simp [Component.Covers]) _)
    (sldt_r16_rex_effect_step p rex hrex modrm hmod hreg v)

theorem sldt_r64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (v : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p (encodeSldtR64 dst))
      (Effect.post (sldtREffect p 4 64 (dst.setWidth 5) v)) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩ := encodeSldtR64_spec dst
  rw [hbytes, ← hdst]
  exact sldt_r64_triple_of_bytes p rex hrex modrm hmod hreg v

theorem sldt_r32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (v : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p (encodeSldtR32 dst))
      (Effect.post (sldtREffect p (encodeSldtR32 dst).length 32 (dst.setWidth 5) v)) := by
  rcases encodeSldtR32_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact sldt_r32_triple_of_bytes p modrm hmod hreg v
  · rw [hbytes, ← hdst]
    exact sldt_r32_rex_triple_of_bytes p rex hrex modrm hmod hreg v

theorem sldt_r16_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) (v : BitVec 16) :
    Triple (fun s => s.RIP = p ∧ SysRegReadable s ∧ s.LDTR.selector = v)
      (codeRange p (encodeSldtR16 dst))
      (Effect.post (sldtREffect p (encodeSldtR16 dst).length 16 (dst.setWidth 5) v)) := by
  rcases encodeSldtR16_spec dst with ⟨modrm, hbytes, hmod, hreg, hdst⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hdst⟩
  · rw [hbytes, ← hdst]
    exact sldt_r16_triple_of_bytes p modrm hmod hreg v
  · rw [hbytes, ← hdst]
    exact sldt_r16_rex_triple_of_bytes p rex hrex modrm hmod hreg v

attribute [x86_compose] sldtREffect

@[x86_local] theorem sldtREffect_local {p : BitVec 64} {len n : Nat} {dst : BitVec 5}
    {v : BitVec 16} :
    Effect.Local (sldtREffect p len n dst v) := by
  effect_local [sldtREffect]

end X86Proofs
