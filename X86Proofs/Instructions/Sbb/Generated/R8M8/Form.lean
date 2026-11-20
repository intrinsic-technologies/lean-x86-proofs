import X86Proofs.Step.Address
import X86Proofs.Instructions.Sbb.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem sbb_r8_m8_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3) (haddr : ctx.address_size = asz)
    (hreg : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.SBB_GPR8_MEMb ip ctx mod reg rm).run s =
      let dst : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let u := dataAccess t "load"
      (.ok (), writeOutputs u dst
        (sbbSpec (StatusFlags.ofRFLAGS t.RFLAGS).CF (dst.read t) ((Operand.mem lin : Operand 8).read t)) 0
        next) := by
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 8 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.SBB_GPR8_MEMb
  simp only [writeOutputs, Operand.write_reg8, Operand.read_reg8, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) rfl).trans ?_
  refine (specM_bind_run _ _ (s := t) rfl).trans ?_
  refine (specM_bind_run _ _ (readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hreg) hmode)).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.SBB => sbb_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hreg) _ (hmode.of_cs_lma_eq rfl rfl)]

theorem sbb_r8_m8_gpr8_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 1 ≤ 2^32)
    (hmem : ∀ i, i < 1 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.SBB_GPR8_MEMb ip ctx mod reg rm).run s =
      let dst : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)
      let u := dataAccess t "load"
      (.ok (), writeOutputs u dst
        (sbbSpec (StatusFlags.ofRFLAGS t.RFLAGS).CF (dst.read t) ((Operand.mem lin : Operand 8).read t)) 0
        next) := by
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 8 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.SBB_GPR8_MEMb
  simp only [writeOutputs, oracleSkip_zero]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) rfl).trans ?_
  refine (specM_bind_run _ _ (s := t) rfl).trans ?_
  refine (specM_bind_run _ _ (readGPR8_run_gpr8 _ _ _ hmode)).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.SBB => sbb_operation _ 8 (by decide) _ _,
    Write_GPR8 => writeGPR8_run_gpr8 _ _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
