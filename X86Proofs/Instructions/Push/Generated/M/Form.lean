import X86Proofs.Program.ReadWrite.Stack

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem push_m_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true)
    (hosz : ctx.osz_prefix_present = false) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hread : MemReadable t lin 8)
    (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.PUSH_MEMv ip ctx mod rm).run s =
      (.ok (), pushState (withNextIP (dataAccess t "load") next)
        ((Operand.mem lin : Operand 64).read t)) := by
  have hread' := logicalMemRead_run_seg t h seg addr lin hseg 64 (by decide) .Memory_Read
    (.inl rfl) hread.low hread.mem
  have hpush := push_operation (withNextIP (dataAccess t "load") next)
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) hss ((Operand.mem lin : Operand 64).read t) (hw.of_external_eq rfl)
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, address_size := asz,
      lock_prefix_present := false, rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hea ⊢
  generalize ctx.rex_w = w at hea ⊢
  rcases hw1 w with rfl | rfl <;>
  · unfold X86.Instructions.PUSH_MEMv
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Read => hread', X86.Instructions.Operations.PUSH => hpush]

theorem push_m16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true)
    (hosz : ctx.osz_prefix_present = true) (hw0 : ctx.rex_w = 0) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hread : MemReadable t lin 2)
    (hw : MemWritable t (pushAddr16 t) 2) :
    (X86.Instructions.PUSH_MEMv ip ctx mod rm).run s =
      (.ok (), pushState16 (withNextIP (dataAccess t "load") next)
        ((Operand.mem lin : Operand 16).read t)) := by
  have hread' := logicalMemRead_run_seg t h seg addr lin hseg 16 (by decide) .Memory_Read
    (.inl rfl) hread.low hread.mem
  have hpush := push16_operation (withNextIP (dataAccess t "load") next)
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) hss ((Operand.mem lin : Operand 16).read t) (hw.of_external_eq rfl)
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := true, address_size := asz,
      lock_prefix_present := false, rex_w := 0 } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hea ⊢
  unfold X86.Instructions.PUSH_MEMv
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread', X86.Instructions.Operations.PUSH => hpush]

end X86Proofs
