import X86Proofs.Instructions.Loop.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem loop_rel8_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (disp : BitVec 8) (haddr : ctx.address_size = 64) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (hready : BranchReady v)
    (htarget : loopTaken .LOOP (rcx.read v - 1) (StatusFlags.ofRFLAGS v.RFLAGS).ZF = true →
      (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.LOOP_RELBRb ip ctx).run u =
      (.ok (), loopState (withNextIP v (BitVec.add ip 1#64))
        (loopTaken .LOOP (rcx.read v - 1) (StatusFlags.ofRFLAGS v.RFLAGS).ZF)
        (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64))) := by
  have hcontext : { ctx with address_size := 64 } = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.LOOP_RELBRb
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := v)
    (value := BitVec.add ip 1#64) rfl).trans ?_
  refine (specM_bind_run _ _ (s := v) (t := withNextIP v (BitVec.add ip 1#64)) (value := ())
    rfl).trans ?_
  have hd : BitVec.ofInt (Int.toNat 8) disp.toInt = disp := by simp
  rw [hd]
  exact loop_operation _ _ _ _ (hmode.of_cs_lma_eq rfl rfl) (hready.withNextIP _) htarget

theorem loop_rel8_a32_form [Bindings] (u v : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (disp : BitVec 8) (haddr : ctx.address_size = 32)
    (hlock : ctx.lock_prefix_present = false) (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (hready : BranchReady v)
    (htarget : loopTaken .LOOP (loopCount32 v) (StatusFlags.ofRFLAGS v.RFLAGS).ZF = true →
      (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.LOOP_RELBRb ip ctx).run u =
      (.ok (), loop32State (withNextIP v (BitVec.add ip 1#64))
        (loopTaken .LOOP (loopCount32 v) (StatusFlags.ofRFLAGS v.RFLAGS).ZF)
        (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64))) := by
  have hcontext : { ctx with address_size := 32 } = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.LOOP_RELBRb
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := v)
    (value := BitVec.add ip 1#64) rfl).trans ?_
  refine (specM_bind_run _ _ (s := v) (t := withNextIP v (BitVec.add ip 1#64)) (value := ())
    rfl).trans ?_
  have hd : BitVec.ofInt (Int.toNat 8) disp.toInt = disp := by simp
  rw [hd]
  exact loop32_operation _ _ _ _ (hmode.of_cs_lma_eq rfl rfl) (hready.withNextIP _) htarget

end X86Proofs
