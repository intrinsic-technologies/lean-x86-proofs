import X86Proofs.Program.ReadWrite.Stack

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pop_r_8f_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 8) :
    (X86.Instructions.POP_GPRv_8F ip ctx rm).run t =
      (.ok (), popState { t with Next_IP := ip } (gprNumber ctx.rex_b4 ctx.rex_b3 rm)) := by
  have hpop := pop_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hr.of_external_eq rfl)
  simp only [popState, Operand.write_reg64]
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = w
  rcases hw1 w with rfl | rfl <;>
  · unfold X86.Instructions.POP_GPRv_8F
    spec_run [X86.Instructions.Operations.POP => hpop, Write_RSP => writeRSP64_run _ _]
    refine (writeGPR64_run _ _ _ ?_).trans ?_
    · exact hmode.of_cs_lma_eq rfl rfl
    · simp only [Operand.write_reg64]
      rfl

theorem pop_r16_8f_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = true)
    (hw0 : ctx.rex_w = 0) (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 2) :
    (X86.Instructions.POP_GPRv_8F ip ctx rm).run t =
      (.ok (), popState16 { t with Next_IP := ip } (gprNumber ctx.rex_b4 ctx.rex_b3 rm)) := by
  have hpop := pop16_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hr.of_external_eq rfl)
  simp only [popState16, Operand.write_reg16]
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := true, lock_prefix_present := false,
      rex_w := 0 } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.POP_GPRv_8F
  spec_run [X86.Instructions.Operations.POP => hpop, Write_RSP => writeRSP64_run _ _]
  refine (writeGPR16_run _ _ _ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · rfl

end X86Proofs
