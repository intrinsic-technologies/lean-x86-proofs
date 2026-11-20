import X86Proofs.Instructions.Div.Generated.R.Step
import X86Proofs.Instructions.Div.Generated.R.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def divR64Effect (p : BitVec 64) (src : BitVec 5) (s : RamState) : Effect :=
  let t := (Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s
  let r := divResult t ((Operand.reg src : Operand 64).read s)
  { rip := p + 3
    writes := [⟨(Operand.reg 2 : Operand 64), r.2⟩,
      ⟨(Operand.reg 0 : Operand 64), r.1⟩]
    flags := some divFlags }

@[simp] theorem divR64Effect_components (p : BitVec 64) (src : BitVec 5) (s : RamState) :
    (divR64Effect p src s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

theorem divR64Effect_avoids (p : BitVec 64) (src : BitVec 5) (s : RamState) (code : CodeMap) :
    (divR64Effect p src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def divR32Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState) : Effect :=
  let t := (Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s
  let r := divResult t ((Operand.reg src : Operand 32).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), r.2.setWidth 64⟩,
      ⟨(Operand.reg 0 : Operand 64), r.1.setWidth 64⟩]
    flags := some divFlags }

@[simp] theorem divR32Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (s : RamState) : (divR32Effect p len src s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

theorem divR32Effect_avoids (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState)
    (code : CodeMap) : (divR32Effect p len src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

def divR16Effect (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState) : Effect :=
  let t := (Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s
  let r := divResult t ((Operand.reg src : Operand 16).read s)
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 2 : Operand 64), mergeGPR 16 r.2 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(Operand.reg 0 : Operand 64), mergeGPR 16 r.1 ((Operand.reg 0 : Operand 64).read s)⟩]
    flags := some divFlags }

@[simp] theorem divR16Effect_components (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (s : RamState) : (divR16Effect p len src s).components = [.reg 2, .reg 0, .flags, .rip] := rfl

theorem divR16Effect_avoids (p : BitVec 64) (len : Nat) (src : BitVec 5) (s : RamState)
    (code : CodeMap) : (divR16Effect p len src s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [Component.Covers]) code

theorem div_r64_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read s))
      (codeRange p [rex, 0xF7, modrm])
      (divR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, div_r64_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, div_r64_ready h rex modrm,
    ⟨afterStep_writePairOutputs_rip h 3 _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 3 _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [divSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_64, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact divFlags_allows _ _ _

theorem div_r64_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64).read s))
      (codeRange p [rex, 0xF7, modrm])
      (Effect.post (divR64Effect p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => divR64Effect_avoids p _ s _)
    (div_r64_effect_step p rex modrm hrex hmod hreg)

theorem div_r32_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32).read s))
      (codeRange p [0xF7, modrm])
      (divR32Effect p 2 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, div_r32_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, div_r32_ready h modrm,
    ⟨afterStep_writePairOutputs_rip h 2 _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 2 _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [divSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_32, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact divFlags_allows _ _ _

theorem div_r32_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 32).read s))
      (codeRange p [0xF7, modrm])
      (Effect.post (divR32Effect p 2 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => divR32Effect_avoids p _ _ s _)
    (div_r32_effect_step p modrm hmod hreg)

theorem div_r32_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 32).read s))
      (codeRange p [rex, 0xF7, modrm])
      (divR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, div_r32_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, div_r32_rex_ready h rex modrm,
    ⟨afterStep_writePairOutputs_rip h 3 _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 3 _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [divSpec, Operand.read_afterFetches, Operand.read_beforeFetch, mergeGPR_32, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact divFlags_allows _ _ _

theorem div_r32_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 32).read s))
      (codeRange p [rex, 0xF7, modrm])
      (Effect.post (divR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => divR32Effect_avoids p _ _ s _)
    (div_r32_rex_effect_step p rex modrm hrex hmod hreg)

theorem div_r16_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read s))
      (codeRange p [0x66, 0xF7, modrm])
      (divR16Effect p 3 (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, div_r16_step s h modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, div_r16_ready h modrm,
    ⟨afterStep_writePairOutputs_rip h 3 _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 3 _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [divSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact divFlags_allows _ _ _

theorem div_r16_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            ((Operand.reg (gprNumber 0 0 (modrmRm modrm)) : Operand 16).read s))
      (codeRange p [0x66, 0xF7, modrm])
      (Effect.post (divR16Effect p 3 (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => divR16Effect_avoids p _ _ s _)
    (div_r16_effect_step p modrm hmod hreg)

theorem div_r16_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    StepEffect (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read s))
      (codeRange p [0x66, rex, 0xF7, modrm])
      (divR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, hdef⟩
  refine ⟨_, div_r16_rex_step s h rex modrm hrex hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) hdef, div_r16_rex_ready h rex modrm,
    ⟨afterStep_writePairOutputs_rip h 4 _ _ _ _ _ 6 _, ?_,
      StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_writePairOutputs s 4 _ _ _ _ _ 6 _⟩⟩
  · show Operand.read _ _ = _ ∧ Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_afterStep,
      Operand.read_writePairOutputs_fst _ (by decide),
      Operand.read_writePairOutputs_snd _ (by decide)]
    simp only [divSpec, Operand.read_afterFetches, Operand.read_beforeFetch, and_self]
  · simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
    exact divFlags_allows _ _ _

theorem div_r16_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 6) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            ((Operand.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 16).read s))
      (codeRange p [0x66, rex, 0xF7, modrm])
      (Effect.post (divR16Effect p 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => divR16Effect_avoids p _ _ s _)
    (div_r16_rex_effect_step p rex modrm hrex hmod hreg)

theorem div_r64_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s)
            ((Operand.reg (src.setWidth 5) : Operand 64).read s))
      (codeRange p (encodeDivR64 src))
      (Effect.post (divR64Effect p (src.setWidth 5))) := by
  obtain ⟨rex, modrm, hbytes, hrex, hmod, hreg, hsrc⟩ := encodeDivR64_spec src
  rw [hbytes, ← hsrc]
  exact div_r64_triple_of_bytes p rex modrm hrex hmod hreg

theorem div_r32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 32).read s ++ (Operand.reg 0 : Operand 32).read s)
            ((Operand.reg (src.setWidth 5) : Operand 32).read s))
      (codeRange p (encodeDivR32 src))
      (Effect.post (divR32Effect p (encodeDivR32 src).length (src.setWidth 5))) := by
  rcases encodeDivR32_spec src with ⟨modrm, hbytes, hmod, hreg, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hsrc⟩
  · rw [hbytes, ← hsrc]
    exact div_r32_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hsrc]
    exact div_r32_rex_triple_of_bytes p rex modrm hrex hmod hreg

theorem div_r16_triple [Bindings] (p : BitVec 64) (src : BitVec 4) :
    Triple (fun s => s.RIP = p ∧
      DivDefined ((Operand.reg 2 : Operand 16).read s ++ (Operand.reg 0 : Operand 16).read s)
            ((Operand.reg (src.setWidth 5) : Operand 16).read s))
      (codeRange p (encodeDivR16 src))
      (Effect.post (divR16Effect p (encodeDivR16 src).length (src.setWidth 5))) := by
  rcases encodeDivR16_spec src with ⟨modrm, hbytes, hmod, hreg, hsrc⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hsrc⟩
  · rw [hbytes, ← hsrc]
    exact div_r16_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hsrc]
    exact div_r16_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] divR64Effect divR32Effect divR16Effect

@[x86_local] theorem divR64Effect_local {p : BitVec 64} {src : BitVec 5} :
    Effect.Local (divR64Effect p src) := by
  effect_local [divR64Effect, divFlags]

@[x86_local] theorem divR32Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5} :
    Effect.Local (divR32Effect p len src) := by
  effect_local [divR32Effect, divFlags]

@[x86_local] theorem divR16Effect_local {p : BitVec 64} {len : Nat} {src : BitVec 5} :
    Effect.Local (divR16Effect p len src) := by
  effect_local [divR16Effect, divFlags]

end X86Proofs
