import X86Proofs.Instructions.Loop.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem jrcxz_rel8_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (disp : BitVec 8) (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (hready : BranchReady v)
    (htarget : rcx.read v = 0#64 → (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.JRCXZ_RELBRb ip ctx).run u =
      (.ok (), branchState v (rcx.read v == 0#64) (BitVec.add ip 1#64)
        (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64))) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.JRCXZ_RELBRb
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := v)
    (value := BitVec.add ip 1#64) rfl).trans ?_
  refine (specM_bind_run _ _ (s := v) (t := withNextIP v (BitVec.add ip 1#64)) (value := ())
    rfl).trans ?_
  unfold X86.Instructions.Operations.JCXZ
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := withNextIP v (BitVec.add ip 1#64))
    (t := withNextIP v (BitVec.add ip 1#64)) (value := rcx.read v) ?_).trans ?_
  · refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rcx_run _)).trans ?_
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, pure,
      ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.pure]
    rfl
  · refine (specM_bind_run _ _ (s := withNextIP v (BitVec.add ip 1#64))
      (value := rcx.read v == 0#64) rfl).trans ?_
    by_cases hz : rcx.read v = 0#64
    · simp only [hz, beq_self_eq_true, ↓reduceIte]
      spec_bind_with (get_run _)
      spec_bind_with (signExtend64_run _ _)
      spec_bind_with (relativeBranchWrap_run (withNextIP v (BitVec.add ip 1#64)) _ _
        (hmode.of_cs_lma_eq rfl rfl))
      spec_bind_with (get_run _)
      spec_bind_with (checkNewRIP_run _ _ (hready.withNextIP _) (htarget hz))
      exact branchNear_run _ _
    · have hzb : (rcx.read v == 0#64) = false := by simpa using hz
      simp only [hzb, Bool.false_eq_true, ↓reduceIte]
      rfl

theorem jecxz_rel8_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (disp : BitVec 8) (haddr : ctx.address_size = 32) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (hready : BranchReady v)
    (htarget : (rcx.read v).setWidth 32 = 0#32 → (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.JECXZ_RELBRb_1 ip ctx).run u =
      (.ok (), branchState v ((rcx.read v).setWidth 32 == 0#32) (BitVec.add ip 1#64)
        (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64))) := by
  have hc : { ctx with address_size := 32 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.JECXZ_RELBRb_1
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := v)
    (value := BitVec.add ip 1#64) rfl).trans ?_
  refine (specM_bind_run _ _ (s := v) (t := withNextIP v (BitVec.add ip 1#64)) (value := ())
    rfl).trans ?_
  unfold X86.Instructions.Operations.JCXZ
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := withNextIP v (BitVec.add ip 1#64))
    (t := withNextIP v (BitVec.add ip 1#64)) (value := (rcx.read v).setWidth 32) ?_).trans ?_
  · refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rcx_run _)).trans ?_
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, pure,
      ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.pure, BitVec.setWidth_eq_extractLsb']
    rfl
  · have hz0 : (liftM (Std.Bits.Is_Zero (size := 32) ((rcx.read v).setWidth 32)) :
        X86.Runtime.SpecM X86.Exception RamState Bool).run (withNextIP v (BitVec.add ip 1#64)) =
          (.ok ((rcx.read v).setWidth 32 == 0#32), withNextIP v (BitVec.add ip 1#64)) := rfl
    refine (specM_bind_run _ _ hz0).trans ?_
    by_cases hz : (rcx.read v).setWidth 32 = 0#32
    · simp only [hz, beq_self_eq_true, ↓reduceIte]
      spec_bind_with (get_run _)
      spec_bind_with (signExtend64_run _ _)
      spec_bind_with (relativeBranchWrap_run (withNextIP v (BitVec.add ip 1#64)) _ _
        (hmode.of_cs_lma_eq rfl rfl))
      spec_bind_with (get_run _)
      spec_bind_with (checkNewRIP_run _ _ (hready.withNextIP _) (htarget hz))
      exact branchNear_run _ _
    · have hzb : ((rcx.read v).setWidth 32 == 0#32) = false := by simpa using hz
      simp only [hzb, Bool.false_eq_true, ↓reduceIte]
      rfl

end X86Proofs
