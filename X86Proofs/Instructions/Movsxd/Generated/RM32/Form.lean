
import X86Proofs.Step.Address
import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movsxd.Operation

namespace X86Proofs

open X86 X86.Helpers X86.Machine X86.UserProcess

theorem movsxd_r64_m32_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3)
    (hw : ctx.rex_w = 1)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 4 ≤ 2^32)
    (hmem : ∀ i, i < 4 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOVSXD_GPR64_MEMd_0 ip ctx mod reg rm).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst
        (movsxdSpec 64 ((Operand.mem lin : Operand 32).read t)) next) := by
  have hcontext :
      {ctx with
        rex_w := 1, address_size := asz,
        lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 32 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.MOVSXD_GPR64_MEMd_0
  simp only [writeResult, Operand.write_reg64]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    liftM => movsxd_operation _ 32 64 (by decide) _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem movsxd_r32_m32_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 32) (hw : ctx.rex_w = 0)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 4 ≤ 2^32)
    (hmem : ∀ i, i < 4 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOVSXD_GPRz_MEMz ip ctx mod reg rm).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst
        (movsxdSpec 32 ((Operand.mem lin : Operand 32).read t)) next) := by
  have hcontext :
      {ctx with
        operand_size := 32, rex_w := 0, address_size := asz,
        lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 32 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.MOVSXD_GPRz_MEMz
  simp only [writeResult, Operand.write_reg32]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    liftM => movsxd_operation _ 32 32 (by decide) _,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem movsxd_r16_m16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 16) (hw : ctx.rex_w = 0)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOVSXD_GPRz_MEMz ip ctx mod reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst
        (movsxdSpec 16 ((Operand.mem lin : Operand 16).read t)) next) := by
  have hcontext :
      {ctx with
        operand_size := 16, rex_w := 0, address_size := asz,
        lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 16 (by decide) .Memory_Read
    (.inl rfl) hlow hmem
  unfold X86.Instructions.MOVSXD_GPRz_MEMz
  simp only [writeResult, Operand.write_reg16]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    liftM => movsxd_operation _ 16 16 (by decide) _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
