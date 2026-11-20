import X86Proofs.Instructions.Call.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem jmp_m_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hmode64 : ctx.is_mode64 = true) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (h : DataReady t) (hread : MemReadable t lin 8)
    (htarget : ((Operand.mem lin : Operand 64).read t).toNat < 2^32) :
    (X86.Instructions.JMP_MEMv ip ctx mod rm).run s =
      (.ok (), jumpState (dataAccess t "load") next ((Operand.mem lin : Operand 64).read t)) := by
  have hcontext :
      ({ ctx with is_mode64 := true, address_size := asz, lock_prefix_present := false } :
        Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hea
  rw [← hcontext]
  have hread' := logicalMemRead_run_seg t h seg addr lin hseg 64 (by decide) .Memory_Read
    (.inl rfl) hread.low hread.mem
  have hd : DataReady (withNextIP (dataAccess t "load") next) :=
    h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables
  unfold X86.Instructions.JMP_MEMv
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread',
    X86.Instructions.Operations.JMP_NEAR => jmp_operation_abs _ _ _ _ hd.branchReady htarget]

end X86Proofs
