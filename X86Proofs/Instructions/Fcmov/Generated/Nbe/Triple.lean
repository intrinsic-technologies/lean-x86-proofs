
import X86Proofs.Instructions.Fcmov.Generated.Nbe.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fcmovnbeStEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3) (c : Bool)
    (s : RamState) : Effect :=
  x87Effect p len
      [(top, if c then ((Operand.fpr (top + i) : Operand 80).read s) else
      ((Operand.fpr (top) : Operand 80).read s))]
    (if c then ftwSet ((Operand.ftw : Operand 16).read s) top
        (x87Tag ((Operand.fpr (top + i) : Operand 80).read s)) else
        ((Operand.ftw : Operand 16).read s))
    (((Operand.fsw : Operand 16).read s)) (0) (0) s

@[simp] theorem fcmovnbeStEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (i : BitVec 3) (c : Bool) (s : RamState) :
    (fcmovnbeStEffect p len top i c s).components = [.fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] :=
        rfl

theorem fcmovnbe_st_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3)
    (c : Bool) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ condHolds 7 (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p [0xDB, modrmRegs 2 i]) (fcmovnbeStEffect p 2 top i c) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hsrc, hc⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fcmovnbe_st_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl (modrmRegs 2 i)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _) h0
        (by simpa only [modrmRm_modrmRegs] using hsrc) c hc hcode.bytesAt hlow
  simp only [modrmRm_modrmRegs] at hstep
  have hh : (fcmovnbeStEffect s.RIP 2 (fswTop s.FP87_Status) i c s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 3) _
      (fun t => if c then fprSet t.FP87 (fswTop t.FP87_Status)
          t.FP87[fprIndex (fswTop t.FP87_Status + i)] else t.FP87)
      (fun t => if c then ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
          (x87Tag t.FP87[fprIndex (fswTop t.FP87_Status + i)]) else t.FP87_Tag_Word)
      (fun t => fcmovStatus t.FP87_Status t.oracle) _ _ _ _
      (by
        intro rv hrv
        simp only [List.mem_singleton] at hrv
        subst hrv
        cases c
        · rfl
        · exact fprSet_get_self _ _ _)
      (by
        intro r hr
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
        cases c
        · rfl
        · exact fprSet_get_of_ne _ (Ne.symm hr) _)
      (by
        cases c <;> x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fcmovStatus]
        rfl)
      (by
        exact BitVec.and_zero)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fcmovnbe_st_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) (c : Bool) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ condHolds 7 (StatusFlags.ofRFLAGS s.RFLAGS) = c)
      (codeRange p [0xDB, modrmRegs 2 i]) (Effect.post (fcmovnbeStEffect p 2 top i c)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fcmovnbeStEffect_components]; simp [Component.Covers]) _)
    (fcmovnbe_st_effect_step p top i c)

attribute [x86_compose] fcmovnbeStEffect

@[x86_local] theorem fcmovnbeStEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {i : BitVec 3} {c : Bool} :
    Effect.Local (fcmovnbeStEffect p len top i c) := by
  effect_local [fcmovnbeStEffect, x87Effect]

end X86Proofs
