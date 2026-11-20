
import X86Proofs.Instructions.Fyl2x.Generated.Fyl2x.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fyl2xEffect [Bindings] (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len
      [(top + 1,
      (x87BindVal
      (FP87.Log2_Multiply ((Operand.fpr (top) : Operand 80).read s)
      ((Operand.fpr (top + 1) : Operand 80).read s)) ((Operand.fcw : Operand 16).read s)).1)]
    (ftwSet
        (ftwSet ((Operand.ftw : Operand 16).read s) (top + 1)
        (x87Tag
        (x87BindVal
        (FP87.Log2_Multiply ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + 1) : Operand 80).read s)) ((Operand.fcw : Operand 16).read s)).1)) top
        3)
    (fswSetTop
        (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87BindVal
        (FP87.Log2_Multiply ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + 1) : Operand 80).read s)) ((Operand.fcw : Operand 16).read s)).2.2)
        (top + 1)) (2)
        (ccC1
        (x87BindVal
        (FP87.Log2_Multiply ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + 1) : Operand 80).read s)) ((Operand.fcw : Operand 16).read s)).2.1) s

theorem fyl2xEffect_components [Bindings] (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (s : RamState) :
    (fyl2xEffect p len top s).components = [.fpr (top + 1), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

attribute [simp] fyl2xEffect_components

theorem fyl2x_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 1) ≠ 3 ∧ X87BindOk
        (FP87.Log2_Multiply s.FP87[fprIndex (top)] s.FP87[fprIndex (top + 1)]) s.FP87_Control)
      (codeRange p [0xD9, 0xF1]) (fyl2xEffect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, h1, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fyl2x_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xF1 (by decide)
    (by decide) (by decide) h0 h1 hok hcode.bytesAt hlow
  have hh : (fyl2xEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 6) _
      (fun t => fprSet t.FP87 (fswTop t.FP87_Status + 1)
          (x87BindVal
          (FP87.Log2_Multiply t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)]) t.FP87_Control).1)
      (fun t => ftwSet
          (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status + 1)
          (x87Tag
          (x87BindVal
          (FP87.Log2_Multiply t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)]) t.FP87_Control).1)) (fswTop t.FP87_Status) 3)
      (fun t => x87ArithFsw (fswSetTop t.FP87_Status (fswTop t.FP87_Status + 1)) t.FP87_Status
          t.oracle
          (x87BindVal
          (FP87.Log2_Multiply t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)]) t.FP87_Control).2.1
          (x87BindVal
          (FP87.Log2_Multiply t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)]) t.FP87_Control).2.2) _ _ _ _
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

theorem fyl2x_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 1) ≠ 3 ∧ X87BindOk
        (FP87.Log2_Multiply s.FP87[fprIndex (top)] s.FP87[fprIndex (top + 1)]) s.FP87_Control)
      (codeRange p [0xD9, 0xF1]) (Effect.post (fyl2xEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fyl2xEffect_components]; simp [Component.Covers]) _)
    (fyl2x_effect_step p top)

attribute [x86_compose] fyl2xEffect

@[x86_local] theorem fyl2xEffect_local [Bindings] {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fyl2xEffect p len top) := by
  effect_local [fyl2xEffect, x87Effect]

end X86Proofs
