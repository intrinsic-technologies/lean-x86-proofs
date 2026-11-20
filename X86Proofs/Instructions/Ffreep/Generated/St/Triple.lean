
import X86Proofs.Instructions.Ffreep.Generated.St.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def ffreepStEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3) (s : RamState) :
    Effect :=
  x87Effect p len []
    (ftwSet (ftwSet ((Operand.ftw : Operand 16).read s) (top + i) 3) top 3)
    (fswSetTop ((Operand.fsw : Operand 16).read s) (top + 1)) (2) (0) s

@[simp] theorem ffreepStEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (i : BitVec 3) (s : RamState) :
    (ffreepStEffect p len top i s).components = [.ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem ffreep_st_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    StepEffect (fun s => X87Pre p top s)
      (codeRange p [0xDF, modrmRegs 0 i]) (ffreepStEffect p 2 top i) := by
  rintro s h hcode ⟨hp, hcr0, hes, _, hfdp, htop⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := ffreep_st_step s h hcr0 hes hfdp [] (by simp) (by simp) rfl rfl (modrmRegs 0 i)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _) hcode.bytesAt hlow
  simp only [modrmRm_modrmRegs] at hstep
  have hh : (ffreepStEffect s.RIP 2 (fswTop s.FP87_Status) i s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 3) _
      (fun t => t.FP87)
      (fun t => ftwSet (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status + i) 3) (fswTop t.FP87_Status)
          3)
      (fun t => fswSetTop (fswC1Zero t.FP87_Status t.oracle) (fswTop t.FP87_Status + 1)) _ _ _ _
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => rfl)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_fswC1Zero]
        rfl)
      (by
        simp only [fswCC_fswSetTop]
        exact fswCC_fswC1Zero _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem ffreep_st_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    Triple (fun s => X87Pre p top s)
      (codeRange p [0xDF, modrmRegs 0 i]) (Effect.post (ffreepStEffect p 2 top i)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ffreepStEffect_components]; simp [Component.Covers]) _)
    (ffreep_st_effect_step p top i)

attribute [x86_compose] ffreepStEffect

@[x86_local] theorem ffreepStEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {i : BitVec 3} :
    Effect.Local (ffreepStEffect p len top i) := by
  effect_local [ffreepStEffect, x87Effect]

end X86Proofs
