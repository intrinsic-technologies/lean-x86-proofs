import X86Proofs.Instructions.Xlat.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xlat_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (haddr : ctx.address_size = 64) (hb4 : ctx.rex_b4 = 0)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hr : MemReadable t (xlatAddr t) 1) :
    (X86.Instructions.XLAT ip ctx).run t = (.ok (), xlatSpec { t with Next_IP := ip }) := by
  have hop := xlat_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    hds (hr.of_external_eq rfl)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cs h.efer.lma
  have hea : ∃ off next, (Effective_Address 64 ctx 0 0 1 ip).run t =
      (.ok (off, nullDataSegment t.DS, next, false, false), t) := by
    have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
    rcases hw1 ctx.rex_b3 with h0 | h1
    · have := effectiveAddress_base_none_run t ctx ip 0 (by decide) (by decide) h0 hb4 hm64 hmode
      rw [effSegment_of_not hseg] at this
      exact ⟨_, _, this⟩
    · have := effectiveAddress_base_none_run t ctx ip 8 (by decide) (by decide) h1 hb4 hm64 hmode
      rw [effSegment_of_not hseg] at this
      exact ⟨_, _, this⟩
  obtain ⟨off, next, hea⟩ := hea
  unfold X86.Instructions.XLAT
  simp only [haddr, hlock, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ hea).trans ?_
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

end X86Proofs
