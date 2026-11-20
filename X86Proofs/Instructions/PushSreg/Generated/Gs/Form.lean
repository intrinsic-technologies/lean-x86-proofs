import X86Proofs.Instructions.PushSreg.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem push_gs_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (h : DataReady t) (hmode : In64BitMode t)
    (hss : t.SS = userStackSegment) (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.PUSH_GS ip ctx).run t =
      (.ok (), pushState { t with Next_IP := ip } (pushsregSpec 64 t.GS.selector)) := by
  have hop := pushsreg_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    t.GS.selector (hw.of_external_eq rfl) (hmode.of_cs_lma_eq rfl rfl)
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = w
  rcases hw1 w with rfl | rfl <;>
  · unfold X86.Instructions.PUSH_GS
    spec_run [MonadState.get => get_run _, X86.Instructions.Operations.PUSH_SEG => hop]

theorem push16_gs_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = true) (hw0 : ctx.rex_w = 0)
    (hlock : ctx.lock_prefix_present = false) (h : DataReady t) (hmode : In64BitMode t)
    (hss : t.SS = userStackSegment) (hw : MemWritable t (pushAddr16 t) 2) :
    (X86.Instructions.PUSH_GS ip ctx).run t =
      (.ok (), pushState16 { t with Next_IP := ip } (pushsregSpec 16 t.GS.selector)) := by
  have hop := pushsreg16_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    t.GS.selector (hw.of_external_eq rfl) (hmode.of_cs_lma_eq rfl rfl)
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := true, lock_prefix_present := false,
      rex_w := 0 } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.PUSH_GS
  spec_run [MonadState.get => get_run _, X86.Instructions.Operations.PUSH_SEG => hop]

end X86Proofs
