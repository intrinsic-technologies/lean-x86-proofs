import X86Proofs.Instructions.Pushf.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pushfq_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) (hosz : ctx.osz_prefix_present = false) (hw : ctx.rex_w = 0)
    (h : DataReady t) (hss : t.SS = userStackSegment)
    (hwr : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.PUSHFQ_0 ip ctx).run t =
      (.ok (), pushState { t with Next_IP := ip }
        (pushfSpec t.RFLAGS)) := by
  have hop := pushfq_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hwr.of_external_eq rfl)
  have hcontext : { ctx with lock_prefix_present := false, osz_prefix_present := false, rex_w := 0 } = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.PUSHFQ_0
  spec_run [X86.Instructions.Operations.PUSHF => hop]

theorem pushf_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) (hw : ctx.rex_w = 0)
    (h : DataReady t) (hss : t.SS = userStackSegment)
    (hwr : MemWritable t (pushAddr16 t) 2) :
    (X86.Instructions.PUSHF_2 ip ctx).run t =
      (.ok (), pushState16 { t with Next_IP := ip }
        ((pushfSpec t.RFLAGS).setWidth 16)) := by
  have hop := pushf_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hwr.of_external_eq rfl)
  have hcontext : { ctx with lock_prefix_present := false, rex_w := 0 } = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.PUSHF_2
  spec_run [X86.Instructions.Operations.PUSHF => hop]

theorem pushfq_rexw_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) (hw : ctx.rex_w = 1)
    (h : DataReady t) (hss : t.SS = userStackSegment)
    (hwr : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.PUSHFQ_1 ip ctx).run t =
      (.ok (), pushState { t with Next_IP := ip }
        (pushfSpec t.RFLAGS)) := by
  have hop := pushfq_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hwr.of_external_eq rfl)
  have hcontext : { ctx with lock_prefix_present := false, rex_w := 1 } = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.PUSHFQ_1
  spec_run [X86.Instructions.Operations.PUSHF => hop]

end X86Proofs
