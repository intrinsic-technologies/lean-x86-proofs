import X86Proofs.Instructions.Call.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem ret_imm16_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (imm : BitVec 16) (hmode64 : ctx.is_mode64 = true) (hlock : ctx.lock_prefix_present = false)
    (hmodeu : In64BitMode u) (hssu : u.SS = userStackSegment)
    (hfetch : (Mem_Fetch ip 16).run u = (.ok imm, v)) (h : DataReady v)
    (hss : v.SS = userStackSegment) (hr : MemReadable v (stackPtr v) 8)
    (htarget : (stackTop v).toNat < 2^32) :
    (X86.Instructions.RET_NEAR_IMMw ip ctx).run u =
      (.ok (), retImmState (withNextIP v (BitVec.add ip 2#64)) imm) := by
  have hcontext : ({ ctx with is_mode64 := true, lock_prefix_present := false } :
      Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hsas : (Stack_Address_Size u.SS).run u = (.ok 64, u) := by
    rw [hssu]; exact stackAddressSize_run u hmodeu
  unfold X86.Instructions.RET_NEAR_IMMw
  spec_run [MonadState.get => get_run _, Stack_Address_Size => hsas, Mem_Fetch => hfetch,
    X86.Instructions.Operations.RET_NEAR => ret_imm_operation (withNextIP v (BitVec.add ip 2#64))
      (h.withNextIP _) hss (hr.of_external_eq rfl) htarget imm]

end X86Proofs
