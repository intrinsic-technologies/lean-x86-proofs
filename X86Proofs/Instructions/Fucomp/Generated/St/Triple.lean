
import X86Proofs.Instructions.Fucomp.Generated.St.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fucompStEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3) (s : RamState) :
    Effect :=
  x87Effect p len []
    (ftwSet ((Operand.ftw : Operand 16).read s) top 3)
    (fswSetTop
        (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87Compare false ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + i) : Operand 80).read s)).2) (top + 1)) (15)
        (x87CmpCC
        (x87Compare false ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + i) : Operand 80).read s)).1) s

@[simp] theorem fucompStEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (i : BitVec 3) (s : RamState) :
    (fucompStEffect p len top i s).components = [.ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fucomp_st_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ X87CompareOk false s.FP87[fprIndex (top)] s.FP87[fprIndex (top + i)])
      (codeRange p [0xDD, modrmRegs 5 i]) (fucompStEffect p 2 top i) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hsrc, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fucomp_st_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl (modrmRegs 5 i)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _) h0
        (by simpa only [modrmRm_modrmRegs] using hsrc) (by simpa only [modrmRm_modrmRegs] using hok)
        hcode.bytesAt hlow
  simp only [modrmRm_modrmRegs] at hstep
  have hh : (fucompStEffect s.RIP 2 (fswTop s.FP87_Status) i s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 0) _
      (fun t => t.FP87)
      (fun t => ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status) 3)
      (fun t => fswSetTop
          (x87CmpFsw t.FP87_Status
          (x87Compare false t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + i)]).1
          (x87Compare false t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + i)]).2) (fswTop t.FP87_Status + 1)) _ _ _ _
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => rfl)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fswSetTop, fswRest_x87CmpFsw]
        rfl)
      (by
        rw [cc_and_15]
        simp only [fswCC_fswSetTop]
        exact fswCC_x87CmpFsw _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fucomp_st_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ X87CompareOk false s.FP87[fprIndex (top)] s.FP87[fprIndex (top + i)])
      (codeRange p [0xDD, modrmRegs 5 i]) (Effect.post (fucompStEffect p 2 top i)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fucompStEffect_components]; simp [Component.Covers]) _)
    (fucomp_st_effect_step p top i)

attribute [x86_compose] fucompStEffect

@[x86_local] theorem fucompStEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {i : BitVec 3} :
    Effect.Local (fucompStEffect p len top i) := by
  effect_local [fucompStEffect, x87Effect]

end X86Proofs
