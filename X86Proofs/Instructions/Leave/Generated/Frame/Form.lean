import X86Proofs.Program.ReadWrite.Stack

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem leave_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment)
    (hr : MemReadable t ((Operand.reg 5 : Operand 64).read t) 8) :
    (X86.Instructions.LEAVE ip ctx).run t = (.ok (), leaveState { t with Next_IP := ip }) := by
  have hleave := leave_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hmode.of_cs_lma_eq rfl rfl) (hr.of_external_eq rfl)
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = w
  rcases hw1 w with rfl | rfl <;>
  · unfold X86.Instructions.LEAVE
    spec_run [X86.Instructions.Operations.LEAVE => hleave]

theorem leave16_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = true) (hw0 : ctx.rex_w = 0)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment)
    (hr : MemReadable t ((Operand.reg 5 : Operand 64).read t) 2) :
    (X86.Instructions.LEAVE ip ctx).run t =
      (.ok (), leaveState16 { t with Next_IP := ip }) := by
  have hleave := leave16_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hmode.of_cs_lma_eq rfl rfl) (hr.of_external_eq rfl)
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := true, lock_prefix_present := false,
      rex_w := 0 } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.LEAVE
  spec_run [X86.Instructions.Operations.LEAVE => hleave]

end X86Proofs
