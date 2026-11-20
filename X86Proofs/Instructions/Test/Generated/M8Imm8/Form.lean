import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Test.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem test_m8_imm8_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (hu : DataReady u)
    (hlow : lin.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (u.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.TEST_MEMb_IMMb_F6r0 ip ctx mod rm).run s =
      (.ok (), writeFlagsOutputs (dataAccess u "load")
        (testSpec (oracleBit (dataAccess u "load").oracle)
          ((Operand.mem lin : Operand 8).read u) (imm.signExtend 8)) 1
        (BitVec.add next 1#64)) := by
  have hread := logicalMemRead_run_seg u hu seg addr lin hseg 8 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.TEST_MEMb_IMMb_F6r0
  simp only [writeFlagsOutputs]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.TEST => test_operation _ 8 (by decide) _ _]

end X86Proofs
