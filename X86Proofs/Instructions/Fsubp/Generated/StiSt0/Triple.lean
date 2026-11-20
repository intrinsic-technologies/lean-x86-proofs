
import X86Proofs.Instructions.Fsubp.Generated.StiSt0.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fsubpStiSt0Effect (p : BitVec 64) (len : Nat) (top : BitVec 3) (i : BitVec 3) (s : RamState) :
    Effect :=
  x87Effect p len
      [(top + i,
      (x87Arith .sub ((Operand.fcw : Operand 16).read s)
      ((Operand.fpr (top + i) : Operand 80).read s) ((Operand.fpr (top) : Operand 80).read s)).1)]
    (ftwSet
        (ftwSet ((Operand.ftw : Operand 16).read s) (top + i)
        (x87Tag
        (x87Arith .sub ((Operand.fcw : Operand 16).read s)
        ((Operand.fpr (top + i) : Operand 80).read s) ((Operand.fpr (top) : Operand 80).read s)).1))
        top 3)
    (fswSetTop
        (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87Arith .sub ((Operand.fcw : Operand 16).read s)
        ((Operand.fpr (top + i) : Operand 80).read s)
        ((Operand.fpr (top) : Operand 80).read s)).2.2) (top + 1)) (2)
        (ccC1
        (x87Arith .sub ((Operand.fcw : Operand 16).read s)
        ((Operand.fpr (top + i) : Operand 80).read s)
        ((Operand.fpr (top) : Operand 80).read s)).2.1) s

@[simp] theorem fsubpStiSt0Effect_components (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (i : BitVec 3) (s : RamState) :
    (fsubpStiSt0Effect p len top i s).components =
        [.fpr (top + i), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fsubp_sti_st0_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ X87ArithOk .sub s.FP87_Control s.FP87[fprIndex (top + i)]
        s.FP87[fprIndex (top)])
      (codeRange p [0xDE, modrmRegs 5 i]) (fsubpStiSt0Effect p 2 top i) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hsrc, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fsubp_sti_st0_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl
      (modrmRegs 5 i)
    (modrmMod_modrmRegs _ _) (modrmReg_modrmRegs _ _) h0
        (by simpa only [modrmRm_modrmRegs] using hsrc) (by simpa only [modrmRm_modrmRegs] using hok)
        hcode.bytesAt hlow
  simp only [modrmRm_modrmRegs] at hstep
  have hh : (fsubpStiSt0Effect s.RIP 2 (fswTop s.FP87_Status) i s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 6) _
      (fun t => fprSet t.FP87 (fswTop t.FP87_Status + i)
          (x87Arith .sub t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status + i)]
          t.FP87[fprIndex (fswTop t.FP87_Status)]).1)
      (fun t => ftwSet
          (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status + i)
          (x87Tag
          (x87Arith .sub t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status + i)]
          t.FP87[fprIndex (fswTop t.FP87_Status)]).1)) (fswTop t.FP87_Status) 3)
      (fun t => x87ArithFsw (fswSetTop t.FP87_Status (fswTop t.FP87_Status + 1)) t.FP87_Status
          t.oracle
          (x87Arith .sub t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status + i)]
          t.FP87[fprIndex (fswTop t.FP87_Status)]).2.1
          (x87Arith .sub t.FP87_Control t.FP87[fprIndex (fswTop t.FP87_Status + i)]
          t.FP87[fprIndex (fswTop t.FP87_Status)]).2.2) _ _ _ _
      (by
        intro rv hrv
        simp only [List.mem_singleton] at hrv
        subst hrv
        exact fprSet_get_self _ _ _)
      (by
        intro r hr
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
        exact fprSet_get_of_ne _ (Ne.symm hr) _)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_x87ArithFsw_top]
        rfl)
      (by
        exact fswCC_x87ArithFsw _ _ _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fsubp_sti_st0_triple [Bindings] (p : BitVec 64) (top : BitVec 3) (i : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + i) ≠ 3 ∧ X87ArithOk .sub s.FP87_Control s.FP87[fprIndex (top + i)]
        s.FP87[fprIndex (top)])
      (codeRange p [0xDE, modrmRegs 5 i]) (Effect.post (fsubpStiSt0Effect p 2 top i)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fsubpStiSt0Effect_components]; simp [Component.Covers]) _)
    (fsubp_sti_st0_effect_step p top i)

attribute [x86_compose] fsubpStiSt0Effect

@[x86_local] theorem fsubpStiSt0Effect_local {p : BitVec 64} {len : Nat} {top : BitVec 3}
    {i : BitVec 3} :
    Effect.Local (fsubpStiSt0Effect p len top i) := by
  effect_local [fsubpStiSt0Effect, x87Effect]

end X86Proofs
