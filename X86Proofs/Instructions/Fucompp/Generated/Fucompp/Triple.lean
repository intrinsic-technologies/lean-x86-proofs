
import X86Proofs.Instructions.Fucompp.Generated.Fucompp.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def fucomppEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len []
    (ftwSet (ftwSet ((Operand.ftw : Operand 16).read s) top 3) (top + 1) 3)
    (fswSetTop
        (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87Compare false ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + 1) : Operand 80).read s)).2) (top + 1 + 1)) (15)
        (x87CmpCC
        (x87Compare false ((Operand.fpr (top) : Operand 80).read s)
        ((Operand.fpr (top + 1) : Operand 80).read s)).1) s

@[simp] theorem fucomppEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState)
    :
    (fucomppEffect p len top s).components = [.ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem fucompp_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 1) ≠ 3 ∧ X87CompareOk false s.FP87[fprIndex (top)] s.FP87[fprIndex (top + 1)])
      (codeRange p [0xDA, 0xE9]) (fucomppEffect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, h1, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := fucompp_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xE9 (by decide)
    (by decide) (by decide) h0 h1 hok hcode.bytesAt hlow
  have hh : (fucomppEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 0) _
      (fun t => t.FP87)
      (fun t => ftwSet (ftwSet t.FP87_Tag_Word (fswTop t.FP87_Status) 3) (fswTop t.FP87_Status + 1)
          3)
      (fun t => fswSetTop
          (fswSetTop
          (x87CmpFsw t.FP87_Status
          (x87Compare false t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)]).1
          (x87Compare false t.FP87[fprIndex (fswTop t.FP87_Status)]
          t.FP87[fprIndex (fswTop t.FP87_Status + 1)]).2) (fswTop t.FP87_Status + 1))
          (fswTop t.FP87_Status + 1 + 1)) _ _ _ _
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => rfl)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_fswSetTop, fswSetTop_fswSetTop, fswRest_x87CmpFsw]
        rfl)
      (by
        rw [cc_and_15]
        simp only [fswCC_fswSetTop]
        exact fswCC_x87CmpFsw _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem fucompp_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ ftwTag s.FP87_Tag_Word
        (top + 1) ≠ 3 ∧ X87CompareOk false s.FP87[fprIndex (top)] s.FP87[fprIndex (top + 1)])
      (codeRange p [0xDA, 0xE9]) (Effect.post (fucomppEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [fucomppEffect_components]; simp [Component.Covers]) _)
    (fucompp_effect_step p top)

attribute [x86_compose] fucomppEffect

@[x86_local] theorem fucomppEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (fucomppEffect p len top) := by
  effect_local [fucomppEffect, x87Effect]

end X86Proofs
