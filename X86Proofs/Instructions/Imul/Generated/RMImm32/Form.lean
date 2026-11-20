
import X86Proofs.Step.Address
import X86Proofs.Core.Operand
import X86Proofs.Instructions.Imul.Operation

namespace X86Proofs

open X86 X86.Helpers X86.Machine X86.UserProcess

theorem imul_r_m_imm32_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 32)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 32).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 4#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady u) (hmode : In64BitMode u)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (u.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.IMUL_GPRv_MEMv_IMMz ip ctx mod reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let v := dataAccess u "load"
      (.ok (), writeOutputs v dst
        (imulSpec (fun i => oracleBit (oracleSkip v.oracle i)) ((Operand.mem lin : Operand n).read u) (imm.signExtend n)) 4
        (BitVec.add next 4#64)) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg u ht seg addr lin hseg 64 (by decide) .Memory_Read
      (.inl rfl) hlow hmem
    unfold X86.Instructions.IMUL_GPRv_MEMv_IMMz
    simp only [writeOutputs, Operand.write_reg64]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_with hfetch
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by
      show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 4#64)) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
      rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.IMUL_SINGLE => imul_operation _ 64 (by decide) _ _,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext :
        {ctx with operand_size := 32, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg u ht seg addr lin hseg 32 (by decide) .Memory_Read
      (.inl rfl) hlow hmem
    unfold X86.Instructions.IMUL_GPRv_MEMv_IMMz
    simp only [writeOutputs, Operand.write_reg32]
    refine (specM_bind_run _ _ hea).trans ?_
    spec_bind_with hfetch
    spec_bind_rfl
    spec_bind_rfl
    spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by
      show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 4#64)) :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
      rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.IMUL_SINGLE => imul_operation _ 32 (by decide) _ _,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem imul_r16_m16_imm16_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 16)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 16)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 16).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 2#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady u) (hmode : In64BitMode u)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (u.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.IMUL_GPRv_MEMv_IMMz ip ctx mod reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let v := dataAccess u "load"
      (.ok (), writeOutputs v dst
        (imulSpec (fun i => oracleBit (oracleSkip v.oracle i)) ((Operand.mem lin : Operand 16).read u) (imm.signExtend 16)) 4
        (BitVec.add next 2#64)) := by
  have hcontext :
      {ctx with operand_size := 16, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg u ht seg addr lin hseg 16 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.IMUL_GPRv_MEMv_IMMz
  simp only [writeOutputs, Operand.write_reg16]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_with hfetch
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by
    show (liftM (Handle_RIP_Relative_Address asz isRip off (BitVec.add next 2#64)) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = _
    rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.IMUL_SINGLE => imul_operation _ 16 (by decide) _ _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
