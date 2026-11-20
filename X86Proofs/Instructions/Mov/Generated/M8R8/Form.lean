import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Mov.Operation

namespace X86Proofs

open X86 X86.Helpers X86.Machine X86.UserProcess

theorem mov_m8_r8_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hreg : ctx.rex_prefix_present = true ∨ (gprNumber ctx.rex_r4 ctx.rex_r3 reg).toNat < 4)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : MemWritable t lin 1) :
    (X86.Instructions.MOV_MEMb_GPR8_1 ip ctx mod reg rm).run s =
      let src : Operand 8 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 8) (movSpec (src.read t))
        next) := by
  have hcontext :
      {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 8 (by decide)
    ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 8).read t) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMb_GPR8_1
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with (readGPR8_run_of_lowByte _ _ _ (lowByte_of_rex hreg) hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]

theorem mov_m8_r8_gpr8_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : MemWritable t lin 1) :
    (X86.Instructions.MOV_MEMb_GPR8_1 ip ctx mod reg rm).run s =
      let src : Operand 8 := .gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 8) (movSpec (src.read t))
        next) := by
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 8 (by decide)
    ((Operand.gpr8 (gprNumber ctx.rex_r4 ctx.rex_r3 reg) (byteRex ctx)).read t) hw.low
    hw.mem
  unfold X86.Instructions.MOV_MEMb_GPR8_1
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with (readGPR8_run_gpr8 _ _ _ hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]

end X86Proofs
