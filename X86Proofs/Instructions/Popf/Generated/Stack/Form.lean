import X86Proofs.Instructions.Popf.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem popfq_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (h : DataReady t) (hss : t.SS = userStackSegment)
    (hr : MemReadable t (stackPtr t) 8)
    (hiopl : X86.Runtime.Unsigned (t.RFLAGS.extractLsb' 12 2) < t.CPL) :
    (X86.Instructions.POPFQ ip ctx).run t = (.ok (), popfqState { t with Next_IP := ip }) := by
  have hop := popfq_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hr.of_external_eq rfl) hiopl
  have hcontext : { ctx with lock_prefix_present := false } = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.POPFQ
  spec_run [X86.Instructions.Operations.POP_FLAGS => hop]

theorem popf_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (h : DataReady t) (hss : t.SS = userStackSegment)
    (hr : MemReadable t (stackPtr t) 2)
    (hiopl : X86.Runtime.Unsigned (t.RFLAGS.extractLsb' 12 2) < t.CPL) :
    (X86.Instructions.POPF ip ctx).run t = (.ok (), popfState { t with Next_IP := ip }) := by
  have hop := popf_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hr.of_external_eq rfl) hiopl
  have hcontext : { ctx with lock_prefix_present := false } = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.POPF
  spec_run [X86.Instructions.Operations.POP_FLAGS => hop]

end X86Proofs
