
import X86Proofs.Instructions.Ftst.Generated.Ftst.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def ftstEffect (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) : Effect :=
  x87Effect p len []
    (((Operand.ftw : Operand 16).read s))
    (fswOrFlags ((Operand.fsw : Operand 16).read s)
        (x87Compare true ((Operand.fpr (top) : Operand 80).read s) 0).2) (15)
        (x87CmpCC (x87Compare true ((Operand.fpr (top) : Operand 80).read s) 0).1) s

@[simp] theorem ftstEffect_components (p : BitVec 64) (len : Nat) (top : BitVec 3) (s : RamState) :
    (ftstEffect p len top s).components = [.ftw, .fsw, .fcc, .fpuPtr, .rip] := rfl

theorem ftst_effect_step [Bindings] (p : BitVec 64) (top : BitVec 3) :
    StepEffect
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ X87CompareOk true
        s.FP87[fprIndex (top)] 0)
      (codeRange p [0xD9, 0xE4]) (ftstEffect p 2 top) := by
  rintro s h hcode ⟨⟨hp, hcr0, hes, hm, hfdp, htop⟩, h0, hok⟩
  subst hp htop
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hstep := ftst_step s h hcr0 hes hm hfdp [] (by simp) (by simp) rfl rfl 0xE4 (by decide)
    (by decide) (by decide) h0 hok hcode.bytesAt hlow
  have hh : (ftstEffect s.RIP 2 (fswTop s.FP87_Status) s).Holds s _ :=
    x87Effect_holds h 2 s.RIP rfl (fun t => 0) _
      (fun t => t.FP87)
      (fun t => t.FP87_Tag_Word)
      (fun t => x87CmpFsw t.FP87_Status
          (x87Compare true t.FP87[fprIndex (fswTop t.FP87_Status)] 0).1
          (x87Compare true t.FP87[fprIndex (fswTop t.FP87_Status)] 0).2) _ _ _ _
      (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => rfl)
      (by
        x87_simp)
      (by
        simp only [Operand.read_fsw, fswRest_x87CmpFsw]
        rfl)
      (by
        rw [cc_and_15]
        exact fswCC_x87CmpFsw _ _ _)
  exact ⟨_, hstep, h.of_agreesExcept hh.agrees h.memory.tables, hh⟩

theorem ftst_triple [Bindings] (p : BitVec 64) (top : BitVec 3) :
    Triple
        (fun s => X87Pre p top s ∧ ftwTag s.FP87_Tag_Word (top) ≠ 3 ∧ X87CompareOk true
        s.FP87[fprIndex (top)] 0)
      (codeRange p [0xD9, 0xE4]) (Effect.post (ftstEffect p 2 top)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [ftstEffect_components]; simp [Component.Covers]) _)
    (ftst_effect_step p top)

attribute [x86_compose] ftstEffect

@[x86_local] theorem ftstEffect_local {p : BitVec 64} {len : Nat} {top : BitVec 3} :
    Effect.Local (ftstEffect p len top) := by
  effect_local [ftstEffect, x87Effect]

end X86Proofs
