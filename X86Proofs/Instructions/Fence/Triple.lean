import X86Proofs.Instructions.Fence.Step
import X86Proofs.Instructions.Nop.Triple
import X86Proofs.Program.Compose

/-!
# LFENCE, MFENCE, SFENCE triples

A fence has the effect of a NOP of its length (`nopEffect p len`: only RIP moves): the machine is
sequential, so there is no ordering to state. The preconditions ask the CPUID feature the decoder
selects the form by (`FencePre p f`: RIP = `p` and feature `f` reported; SSE2 for LFENCE and
MFENCE, SSE for SFENCE). Triples for any register ModRM byte with the fence's digit
(`<op>_triple_of_modrm`) and for the usual one (`0F AE E8`, `F0`, `F8`: `<op>_triple`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- The precondition of a fence triple at `p`: RIP = `p`, and CPUID reports feature `f`. -/
structure FencePre [Bindings] (p : BitVec 64) (f : CPUID_Feature) (s : RamState) : Prop where
  rip : s.RIP = p
  feature : Prelude.ReportsCPUFeature Bindings.processor s f true

/-- The step behind `lfence_triple_of_modrm`: only RIP moves, to `p + 3`. -/
theorem lfence_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 5) :
    StepEffect (FencePre p CPUID_SSE2_Encoding) (codeRange p [0x0F, 0xAE, modrm])
      (fun _ => nopEffect p 3) := by
  rintro s h hcode ⟨rfl, hfeat⟩
  refine ⟨_, lfence_step s h hfeat [] (by simp) (by simp) rfl rfl rfl rfl modrm hmod hreg
      hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_fence h _ _ _, ?_⟩
  exact ⟨afterStep_fence_rip h _ _ _, trivial, trivial, AgreesExcept.afterStep_fence s _ _ _⟩

/-- The triple for `lfence` (`0F AE /5` with a register ModRM byte) at `p`: only RIP moves. -/
theorem lfence_triple_of_modrm [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 5) :
    Triple (FencePre p CPUID_SSE2_Encoding) (codeRange p [0x0F, 0xAE, modrm])
      (Effect.post fun _ => nopEffect p 3) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p 3 _) (lfence_effect_step p modrm hmod hreg)

/-- The triple for `lfence` (`0F AE E8`) at `p`: only RIP moves, to `p + 3`. -/
theorem lfence_triple [Bindings] (p : BitVec 64) :
    Triple (FencePre p CPUID_SSE2_Encoding) (codeRange p [0x0F, 0xAE, 0xE8])
      (Effect.post fun _ => nopEffect p 3) :=
  lfence_triple_of_modrm p 0xE8 (by decide) (by decide)

/-- The step behind `mfence_triple_of_modrm`: only RIP moves, to `p + 3`. -/
theorem mfence_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 6) :
    StepEffect (FencePre p CPUID_SSE2_Encoding) (codeRange p [0x0F, 0xAE, modrm])
      (fun _ => nopEffect p 3) := by
  rintro s h hcode ⟨rfl, hfeat⟩
  refine ⟨_, mfence_step s h hfeat [] (by simp) (by simp) rfl rfl rfl rfl modrm hmod hreg
      hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_fence h _ _ _, ?_⟩
  exact ⟨afterStep_fence_rip h _ _ _, trivial, trivial, AgreesExcept.afterStep_fence s _ _ _⟩

/-- The triple for `mfence` (`0F AE /6` with a register ModRM byte) at `p`: only RIP moves. -/
theorem mfence_triple_of_modrm [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (FencePre p CPUID_SSE2_Encoding) (codeRange p [0x0F, 0xAE, modrm])
      (Effect.post fun _ => nopEffect p 3) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p 3 _) (mfence_effect_step p modrm hmod hreg)

/-- The triple for `mfence` (`0F AE F0`) at `p`: only RIP moves, to `p + 3`. -/
theorem mfence_triple [Bindings] (p : BitVec 64) :
    Triple (FencePre p CPUID_SSE2_Encoding) (codeRange p [0x0F, 0xAE, 0xF0])
      (Effect.post fun _ => nopEffect p 3) :=
  mfence_triple_of_modrm p 0xF0 (by decide) (by decide)

/-- The step behind `sfence_triple_of_modrm`: only RIP moves, to `p + 3`. -/
theorem sfence_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hreg : modrmReg modrm = 7) :
    StepEffect (FencePre p CPUID_SSE_Encoding) (codeRange p [0x0F, 0xAE, modrm])
      (fun _ => nopEffect p 3) := by
  rintro s h hcode ⟨rfl, hfeat⟩
  refine ⟨_, sfence_step s h hfeat [] (by simp) (by simp) rfl rfl rfl rfl modrm hmod hreg
      hcode.bytesAt (hcode.low (by simp) (by simp)),
    ReadyToStep.afterStep_fence h _ _ _, ?_⟩
  exact ⟨afterStep_fence_rip h _ _ _, trivial, trivial, AgreesExcept.afterStep_fence s _ _ _⟩

/-- The triple for `sfence` (`0F AE /7` with a register ModRM byte) at `p`: only RIP moves. -/
theorem sfence_triple_of_modrm [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) :
    Triple (FencePre p CPUID_SSE_Encoding) (codeRange p [0x0F, 0xAE, modrm])
      (Effect.post fun _ => nopEffect p 3) :=
  Triple.of_effect (fun _ _ => nopEffect_avoids p 3 _) (sfence_effect_step p modrm hmod hreg)

/-- The triple for `sfence` (`0F AE F8`) at `p`: only RIP moves, to `p + 3`. -/
theorem sfence_triple [Bindings] (p : BitVec 64) :
    Triple (FencePre p CPUID_SSE_Encoding) (codeRange p [0x0F, 0xAE, 0xF8])
      (Effect.post fun _ => nopEffect p 3) :=
  sfence_triple_of_modrm p 0xF8 (by decide) (by decide)

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem FencePre.of_holds [Bindings] (h : e.Holds s s') {p : BitVec 64}
    {f : CPUID_Feature} (hrip : e.rip = p)
    (hf : Prelude.ReportsCPUFeature Bindings.processor s f true) : FencePre p f s' :=
  ⟨h.rip_of hrip, h.reportsCPUFeature_iff.mpr hf⟩

end Carry

end X86Proofs
