import X86Proofs.Instructions.Shld.Generated.RRCl.Step
import X86Proofs.Instructions.Shld.Generated.RRCl.Encode
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Shld.Generated.RRImm8.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def shldR64R64ClEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  shldR64R64Effect p len dst src (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shldR64R64ClEffect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (shldR64R64ClEffect p len dst src s).components =
      [.reg dst, .flags, .rip] := rfl

def shldR32R32ClEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  shldR32R32Effect p len dst src (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shldR32R32ClEffect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (shldR32R32ClEffect p len dst src s).components =
      [.reg dst, .flags, .rip] := rfl

def shldR16R16ClEffect (p : BitVec 64) (len : Nat) (dst src : BitVec 5) (s : RamState) :
    Effect :=
  shldR16R16Effect p len dst src (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shldR16R16ClEffect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (shldR16R16ClEffect p len dst src s).components =
      [.reg dst, .flags, .rip] := rfl

theorem shld_r64_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xA5, modrm]))
      (shldR64R64ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := shld_r_r_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self]
    rw [shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega)]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shldFlags_allows _ _ _ _ _ _

theorem shld_r64_r64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xA5, modrm]))
      (Effect.post (shldR64R64ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shldR64R64ClEffect_components]; simp [Component.Covers]) _)
    (shld_r64_r64_cl_effect_step p rex hrex modrm hmod)

theorem shld_r32_r32_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xA5, modrm]))
      (shldR32R32ClEffect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 3 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := shld_r_r_cl_step s h [] (by simp) (by simp) 32 (.inr rfl)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32]
    rw [shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega)]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shldFlags_allows _ _ _ _ _ _

theorem shld_r32_r32_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([0x0F, 0xA5, modrm]))
      (Effect.post (shldR32R32ClEffect p 3 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shldR32R32ClEffect_components]; simp [Component.Covers]) _)
    (shld_r32_r32_cl_effect_step p modrm hmod)

theorem shld_r32_r32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xA5, modrm]))
      (shldR32R32ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode hp
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := shld_r_r_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32]
    rw [shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega)]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shldFlags_allows _ _ _ _ _ _

theorem shld_r32_r32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p)
      (codeRange p ([rex, 0x0F, 0xA5, modrm]))
      (Effect.post (shldR32R32ClEffect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shldR32R32ClEffect_components]; simp [Component.Covers]) _)
    (shld_r32_r32_cl_rex_effect_step p rex hrex modrm hmod)

theorem shld_r16_r16_cl_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p ([0x66, 0x0F, 0xA5, modrm]))
      (shldR16R16ClEffect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm))) := by
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := shld_r16_r16_cl_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, Operand.read_afterFetches, Operand.read_beforeFetch]
    rw [shldSpec_fst _ _ _ _ hc]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shldFlags_allows _ _ _ _ _ _

theorem shld_r16_r16_cl_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p ([0x66, 0x0F, 0xA5, modrm]))
      (Effect.post (shldR16R16ClEffect p 4 (gprNumber 0 0 (modrmRm modrm))
        (gprNumber 0 0 (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shldR16R16ClEffect_components]; simp [Component.Covers]) _)
    (shld_r16_r16_cl_effect_step p modrm hmod)

theorem shld_r16_r16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p ([0x66, rex, 0x0F, 0xA5, modrm]))
      (shldR16R16ClEffect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hc⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := shld_r16_r16_cl_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
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
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, Operand.read_afterFetches, Operand.read_beforeFetch]
    rw [shldSpec_fst _ _ _ _ hc]
  · simp only [afterFetches_RFLAGS, beforeFetch_RFLAGS]
    exact shldFlags_allows _ _ _ _ _ _

theorem shld_r16_r16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p ([0x66, rex, 0x0F, 0xA5, modrm]))
      (Effect.post (shldR16R16ClEffect p 5 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
        (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [shldR16R16ClEffect_components]; simp [Component.Covers]) _)
    (shld_r16_r16_cl_rex_effect_step p rex hrex modrm hmod)

theorem shld_r64_r64_cl_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeShldR64R64Cl dst src))
      (Effect.post (shldR64R64ClEffect p (encodeShldR64R64Cl dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeShldR64R64Cl_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact shld_r64_r64_cl_triple_of_bytes p rex hrex modrm hmod

theorem shld_r32_r32_cl_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p)
      (codeRange p (encodeShldR32R32Cl dst src))
      (Effect.post (shldR32R32ClEffect p (encodeShldR32R32Cl dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeShldR32R32Cl_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact shld_r32_r32_cl_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact shld_r32_r32_cl_rex_triple_of_bytes p rex hrex modrm hmod

theorem shld_r16_r16_cl_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (encodeShldR16R16Cl dst src))
      (Effect.post (shldR16R16ClEffect p (encodeShldR16R16Cl dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeShldR16R16Cl_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact shld_r16_r16_cl_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact shld_r16_r16_cl_rex_triple_of_bytes p rex hrex modrm hmod

attribute [x86_compose] shldR64R64ClEffect shldR32R32ClEffect shldR16R16ClEffect

@[x86_local] theorem shldR64R64ClEffect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} :
    Effect.Local (shldR64R64ClEffect p len dst src) :=
  Effect.Local.of_param (e := fun c => shldR64R64Effect p len dst src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shldR64R64Effect_local

@[x86_local] theorem shldR32R32ClEffect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} :
    Effect.Local (shldR32R32ClEffect p len dst src) :=
  Effect.Local.of_param (e := fun c => shldR32R32Effect p len dst src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shldR32R32Effect_local

@[x86_local] theorem shldR16R16ClEffect_local {p : BitVec 64} {len : Nat}
    {dst src : BitVec 5} :
    Effect.Local (shldR16R16ClEffect p len dst src) :=
  Effect.Local.of_param (e := fun c => shldR16R16Effect p len dst src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shldR16R16Effect_local

end X86Proofs
