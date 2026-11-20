
import X86Proofs.Instructions.Fscale.Generated.Fscale.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fscaleEffect [Bindings] (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len
      [(top,
      (x87BindVal
      (Runtime.liftTotal
      (FP87.Scale ((Operand.fpr (top) : Operand 80).read s)
      ((Operand.fpr (top + 1) : Operand 80).read s))) ((Operand.fcw : Operand 16).read s)).1)]
    (ftwSet ((Operand.ftw : Operand 16).read s) top
        (x87Tag
        (x87BindVal
        (Runtime.liftTotal
        (FP87.Scale ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + 1) : Operand 80).read s))) ((Operand.fcw : Operand 16).read s)).1))
    (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87BindVal
        (Runtime.liftTotal
        (FP87.Scale ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + 1) : Operand 80).read s))) ((Operand.fcw : Operand 16).read s)).2.2)
        (2)
        (ccC1
        (x87BindVal
        (Runtime.liftTotal
        (FP87.Scale ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + 1) : Operand 80).read s))) ((Operand.fcw : Operand 16).read s)).2.1) s

theorem fscaleEffect_components [Bindings] (p : BitVec 64) (len : Nat) (top : BitVec 3)
    (s : RamState) :
    (fscaleEffect p len top s).components = [.fpr (top), .ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

attribute [simp] fscaleEffect_components

theorem fscale_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 1) ≠ 3 ∧ X87BindOk
        (Runtime.liftTotal (FP87.Scale s.FP87[fprIndex (top)] s.FP87[fprIndex (top + 1)]))
        s.FP87_Control)
      (codeRange p [0xD9, 0xFD]) (fscaleEffect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, h1, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fscale_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xFD (by decide)
    (by decide) (by decide) h0 h1 hok hcode.bytesAt hlow
  have hh : (fscaleEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 6) _
      (fun t => fprSet t.FP87 (fswTop t.FP87_Status)
          (x87BindVal
          (Runtime.liftTotal
          (FP87.Scale t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)])) t.FP87_Control).1)
      (fun t => ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status)
          (x87Tag
          (x87BindVal
          (Runtime.liftTotal
          (FP87.Scale t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)])) t.FP87_Control).1))
      (fun t => x87ArithFsw t.FP87_Status t.FP87_Status t.oracle
          (x87BindVal
          (Runtime.liftTotal
          (FP87.Scale t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)])) t.FP87_Control).2.1
          (x87BindVal
          (Runtime.liftTotal
          (FP87.Scale t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)])) t.FP87_Control).2.2) _ _ _ _
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
        simp only [Operand.read_fsw, fswRest_x87ArithFsw]
        rfl)
      (by
        exact fswCC_x87ArithFsw _ _ _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fscale_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 1) ≠ 3 ∧ X87BindOk
        (Runtime.liftTotal (FP87.Scale s.FP87[fprIndex (top)] s.FP87[fprIndex (top + 1)]))
        s.FP87_Control)
      (codeRange p [0xD9, 0xFD]) (Effect.post (fscaleEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fscaleEffect_components]; simp [Component.Covers]) _)
    (fscale_effect_step p top)

attribute [x86_compose] fscaleEffect

@[x86_local] theorem fscaleEffect_local [Bindings] {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fscaleEffect p len top) := by
  effect_local [fscaleEffect, x87Effect]

end X86Proofs
