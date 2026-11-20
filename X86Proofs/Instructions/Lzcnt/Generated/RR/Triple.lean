import X86Proofs.Instructions.Lzcnt.Generated.RR.Step
import X86Proofs.Instructions.Lzcnt.Generated.RR.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def lzcntR64R64Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      BitVec.ofNat 64 (leadingZeros x)⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR64R64Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (lzcntR64R64Effect p len dst src s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR32R32Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (BitVec.ofNat 32 (leadingZeros x)).setWidth 64⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR32R32Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (lzcntR32R32Effect p len dst src s).components = [.reg dst, .flags, .rip] := rfl

def lzcntR16R16Effect (p : BitVec 64) (len : Nat) (dst src : BitVec 5)
    (s : RamState) : Effect :=
  let x := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      mergeGPR 16 (BitVec.ofNat 16 (leadingZeros x)) ((Operand.reg dst : Operand 64).read s)⟩]
    flags := some (lzcntFlags x) }

@[simp] theorem lzcntR16R16Effect_components (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) (s : RamState) :
    (lzcntR16R16Effect p len dst src s).components = [.reg dst, .flags, .rip] := rfl

theorem lzcnt_r64_r64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p ([0xF3, rex, 0x0F, 0xBD, modrm]))
      (lzcntR64R64Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hl⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := lzcnt_r_r_step s h [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp) 64 (.inl rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl) (by rw [scanContext_f3_rex _ _ hr]; rfl) (by rw [scanContext_f3_rex _ _ hr]; rfl) hl modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_f3_rex _ _ hr] at hstep
  have hdst : gprNumber (repRexContext s.DS rex.toBitVec).rex_r4 (repRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (repRexContext s.DS rex.toBitVec).rex_b4 (repRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r64_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p ([0xF3, rex, 0x0F, 0xBD, modrm]))
      (Effect.post (lzcntR64R64Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR64R64Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r64_r64_effect_step p rex hrex modrm hmod)

theorem lzcnt_r32_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p ([0xF3, 0x0F, 0xBD, modrm]))
      (lzcntR32R32Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨hp, hl⟩
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := lzcnt_r_r_step s h [0xF3] (by simpa using scanPrefix_f3) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl) (by rfl) hl modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) [0xF3]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r32_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p ([0xF3, 0x0F, 0xBD, modrm]))
      (Effect.post (lzcntR32R32Effect p 4 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR32R32Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r32_r32_effect_step p modrm hmod)

theorem lzcnt_r32_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p ([0xF3, rex, 0x0F, 0xBD, modrm]))
      (lzcntR32R32Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hl⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := lzcnt_r_r_step s h [0xF3, rex] (by simp [scanPrefix_f3, hr.scanPrefix]) (by simp) 32 (.inr rfl)
    (by rw [scanContext_f3_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_f3_rex _ _ hr]; rfl) (by rw [scanContext_f3_rex _ _ hr]; rfl) (by rw [scanContext_f3_rex _ _ hr]; rfl) hl modrm hmod
    hcode.bytesAt hlow
  simp only [scanContext_f3_rex _ _ hr] at hstep
  have hdst : gprNumber (repRexContext s.DS rex.toBitVec).rex_r4 (repRexContext s.DS rex.toBitVec).rex_r3 (modrmReg modrm) =
      (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) := rfl
  have hsrc : gprNumber (repRexContext s.DS rex.toBitVec).rex_b4 (repRexContext s.DS rex.toBitVec).rex_b3 (modrmRm modrm) =
      (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self32, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r32_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8) (hrex : RexNoWPrefix rex.toBitVec) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p ([0xF3, rex, 0x0F, 0xBD, modrm]))
      (Effect.post (lzcntR32R32Effect p 5 (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
        (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR32R32Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r32_r32_rex_effect_step p rex hrex modrm hmod)

theorem lzcnt_r16_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    StepEffect (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p ([0x66, 0xF3, 0x0F, 0xBD, modrm]))
      (lzcntR16R16Effect p 5 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨hp, hl⟩
  subst hp
  have hlow : s.RIP.toNat + 5 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := lzcnt_r16_r16_step s h [0x66, 0xF3] (by simp [scanPrefix_66, scanPrefix_f3]) (by simp)
    (by exact rfl)
    (by rfl) (by rfl) (by rfl) hl modrm hmod
    hcode.bytesAt hlow
  dsimp only at hstep
  have hdst : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]).rex_r4 (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]).rex_r3 (modrmReg modrm) =
      (gprNumber 0 0 (modrmReg modrm)) := rfl
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) [0x66, 0xF3]).rex_b3 (modrmRm modrm) =
      (gprNumber 0 0 (modrmRm modrm)) := rfl
  rw [hdst, hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_writeOutputs h _ _ _ _ _,
    ⟨afterStep_writeOutputs_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writeOutputs s _ _ _ _ _⟩⟩
  · show Operand.read _ _ = _
    rw [Operand.read_afterStep]
    simp only [Operand.read_writeOutputs_self_merge, lzcntSpec, Operand.read_afterFetches,
      Operand.read_beforeFetch]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact lzcntFlags_allows _ _

theorem lzcnt_r16_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) :
    Triple (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true)
      (codeRange p ([0x66, 0xF3, 0x0F, 0xBD, modrm]))
      (Effect.post (lzcntR16R16Effect p 5 (gprNumber 0 0 (modrmReg modrm))
        (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [lzcntR16R16Effect_components]; simp [Component.Covers]) _)
    (lzcnt_r16_r16_effect_step p modrm hmod)

theorem lzcnt_r64_r64_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true) (codeRange p (encodeLzcntR64R64 dst src))
      (Effect.post (lzcntR64R64Effect p (encodeLzcntR64R64 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩ := encodeLzcntR64R64_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact lzcnt_r64_r64_triple_of_bytes p rex hrex modrm hmod

theorem lzcnt_r32_r32_triple [Bindings] (p : BitVec 64) (dst src : BitVec 4) :
    Triple (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true) (codeRange p (encodeLzcntR32R32 dst src))
      (Effect.post (lzcntR32R32Effect p (encodeLzcntR32R32 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  rcases encodeLzcntR32R32_spec dst src with ⟨modrm, hbytes, hmod, hdst, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hdst, hsrc⟩
  · rw [hbytes, ← hdst, ← hsrc]
    exact lzcnt_r32_r32_triple_of_bytes p modrm hmod
  · rw [hbytes, ← hdst, ← hsrc]
    exact lzcnt_r32_r32_rex_triple_of_bytes p rex hrex modrm hmod

theorem lzcnt_r16_r16_triple [Bindings] (p : BitVec 64) (dst src : BitVec 3) :
    Triple (fun s => s.RIP = p ∧ Prelude.ReportsCPUFeature Bindings.processor s CPUID_LZCNT_Encoding true) (codeRange p (encodeLzcntR16R16 dst src))
      (Effect.post (lzcntR16R16Effect p (encodeLzcntR16R16 dst src).length (dst.setWidth 5)
        (src.setWidth 5))) := by
  obtain ⟨modrm, hbytes, hmod, hdst, hsrc⟩ := encodeLzcntR16R16_spec dst src
  rw [hbytes, ← hdst, ← hsrc]
  exact lzcnt_r16_r16_triple_of_bytes p modrm hmod

attribute [x86_compose] lzcntR64R64Effect lzcntR32R32Effect lzcntR16R16Effect lzcntFlags

@[x86_local] theorem lzcntR64R64Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (lzcntR64R64Effect p len dst src) := by
  effect_local [lzcntR64R64Effect, lzcntFlags]

@[x86_local] theorem lzcntR32R32Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (lzcntR32R32Effect p len dst src) := by
  effect_local [lzcntR32R32Effect, lzcntFlags]

@[x86_local] theorem lzcntR16R16Effect_local {p : BitVec 64} {len : Nat} {dst : BitVec 5}
    {src : BitVec 5} :
    Effect.Local (lzcntR16R16Effect p len dst src) := by
  effect_local [lzcntR16R16Effect, lzcntFlags]

end X86Proofs
