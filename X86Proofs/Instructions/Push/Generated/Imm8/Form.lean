import X86Proofs.Program.ReadWrite.Stack

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem push_imm8_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (imm : BitVec 8) (hmode64 : ctx.is_mode64 = true)
    (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run u = (.ok imm, v)) (h : DataReady v)
    (hss : v.SS = userStackSegment) (hw : MemWritable v (pushAddr v) 8) :
    (X86.Instructions.PUSH_IMMb ip ctx).run u =
      (.ok (), pushState { v with Next_IP := BitVec.add ip 1#64 } (imm.signExtend 64)) := by
  have hpush := push_operation { v with Next_IP := BitVec.add ip 1#64 } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (imm.signExtend 64) (hw.of_external_eq rfl)
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = w
  rcases hw1 w with rfl | rfl <;>
  · unfold X86.Instructions.PUSH_IMMb
    spec_run [Mem_Fetch => hfetch, X86.Instructions.Operations.PUSH => hpush]

theorem push16_imm8_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (imm : BitVec 8) (hmode64 : ctx.is_mode64 = true)
    (hosz : ctx.osz_prefix_present = true) (hw0 : ctx.rex_w = 0)
    (hlock : ctx.lock_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run u = (.ok imm, v)) (h : DataReady v)
    (hss : v.SS = userStackSegment) (hw : MemWritable v (pushAddr16 v) 2) :
    (X86.Instructions.PUSH_IMMb ip ctx).run u =
      (.ok (), pushState16 { v with Next_IP := BitVec.add ip 1#64 } (imm.signExtend 16)) := by
  have hpush := push16_operation { v with Next_IP := BitVec.add ip 1#64 } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (imm.signExtend 16) (hw.of_external_eq rfl)
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := true, lock_prefix_present := false,
      rex_w := 0 } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.PUSH_IMMb
  spec_run [Mem_Fetch => hfetch, X86.Instructions.Operations.PUSH => hpush]

end X86Proofs
