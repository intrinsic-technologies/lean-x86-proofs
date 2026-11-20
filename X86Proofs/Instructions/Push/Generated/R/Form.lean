import X86Proofs.Program.ReadWrite.Stack

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem push_r_ff_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.PUSH_GPRv_FFr6 ip ctx rm).run t =
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), pushState { t with Next_IP := ip } (src.read t)) := by
  have hpush := push_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
  simp only [Operand.read_reg64]
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = w
  rcases hw1 w with rfl | rfl <;>
  · unfold X86.Instructions.PUSH_GPRv_FFr6
    spec_run [Read_GPR => readGPR64_run _ _ hmode,
      X86.Instructions.Operations.PUSH => hpush _ (hw.of_external_eq rfl)]

theorem push_r16_ff_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = true)
    (hw0 : ctx.rex_w = 0) (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hw : MemWritable t (pushAddr16 t) 2) :
    (X86.Instructions.PUSH_GPRv_FFr6 ip ctx rm).run t =
      let src : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), pushState16 { t with Next_IP := ip } (src.read t)) := by
  have hpush := push16_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
  simp only [Operand.read_reg16]
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := true, lock_prefix_present := false,
      rex_w := 0 } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.PUSH_GPRv_FFr6
  spec_run [Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.PUSH => hpush _ (hw.of_external_eq rfl)]

end X86Proofs
