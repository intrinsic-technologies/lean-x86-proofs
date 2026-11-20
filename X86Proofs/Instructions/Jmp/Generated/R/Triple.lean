import X86Proofs.Instructions.Jmp.Generated.R.Step
import X86Proofs.Instructions.Jmp.Generated.R.Encode
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def jmpR64Effect (r : BitVec 5) (s : RamState) : Effect :=
  { rip := (Operand.reg r : Operand 64).read s }

@[simp] theorem jmpR64Effect_components (r : BitVec 5) (s : RamState) :
    (jmpR64Effect r s).components = [.rip] := rfl

abbrev JmpRegPre (p : BitVec 64) (r : BitVec 5) (s : RamState) : Prop :=
  s.RIP = p ∧ ((Operand.reg r : Operand 64).read s).toNat < 2^32

theorem jmp_r64_effect_step [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (JmpRegPre p (gprNumber 0 0 (modrmRm modrm))) (codeRange p [0xFF, modrm])
      (jmpR64Effect (gprNumber 0 0 (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, htarget⟩
  exact ⟨_, jmp_r64_step s h [] (by simp) (by simp) rfl rfl rfl modrm hmod hreg hcode.bytesAt
      (hcode.low (by simp) (by simp)) htarget,
    ReadyToStep.afterStep_branchState h _ true _ _, branchEffect_holds h _ true _ _⟩

theorem jmp_r64_triple_of_bytes [Bindings] (p : BitVec 64) (modrm : UInt8)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (JmpRegPre p (gprNumber 0 0 (modrmRm modrm))) (codeRange p [0xFF, modrm])
      (Effect.post (jmpR64Effect (gprNumber 0 0 (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [jmpR64Effect_components]; simp [Component.Covers]) _)
    (jmp_r64_effect_step p modrm hmod hreg)

theorem jmp_r64_rex_effect_step [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    StepEffect (JmpRegPre p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))
      (codeRange p [rex, 0xFF, modrm])
      (jmpR64Effect (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))) := by
  rintro s h hcode ⟨rfl, htarget⟩
  have hstep := jmp_r64_step s h [rex] (by simpa using hrex.scanPrefix) (by simp)
    (by rw [scanContext_rex _ _ hrex]; rfl) (by rw [scanContext_rex _ _ hrex]; rfl)
    (by rw [scanContext_rex _ _ hrex]; rfl) modrm hmod hreg hcode.bytesAt
    (hcode.low (by simp) (by simp)) (by rw [scanContext_rex _ _ hrex]; exact htarget)
  simp only [scanContext_rex _ _ hrex] at hstep
  exact ⟨_, hstep, ReadyToStep.afterStep_branchState h _ true _ _, branchEffect_holds h _ true _ _⟩

theorem jmp_r64_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 4) :
    Triple (JmpRegPre p (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))
      (codeRange p [rex, 0xFF, modrm])
      (Effect.post (jmpR64Effect (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [jmpR64Effect_components]; simp [Component.Covers]) _)
    (jmp_r64_rex_effect_step p rex modrm hrex hmod hreg)

theorem jmp_r64_triple [Bindings] (p : BitVec 64) (r : BitVec 4) :
    Triple (JmpRegPre p (r.setWidth 5)) (codeRange p (encodeJmpR64 r))
      (Effect.post (jmpR64Effect (r.setWidth 5))) := by
  rcases encodeJmpR64_spec r with ⟨modrm, hbytes, hmod, hreg, hr⟩ |
    ⟨rex, modrm, hbytes, hrex, hmod, hreg, hr⟩
  · rw [hbytes, ← hr]
    exact jmp_r64_triple_of_bytes p modrm hmod hreg
  · rw [hbytes, ← hr]
    exact jmp_r64_rex_triple_of_bytes p rex modrm hrex hmod hreg

attribute [x86_compose] jmpR64Effect

@[x86_local] theorem jmpR64Effect_local {r : BitVec 5} : Effect.Local (jmpR64Effect r) := by
  effect_local [jmpR64Effect]

end X86Proofs
