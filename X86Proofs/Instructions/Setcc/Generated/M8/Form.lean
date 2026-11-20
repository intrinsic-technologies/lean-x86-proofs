
import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Setcc.Operation

namespace X86Proofs

open X86 X86.Helpers X86.Machine X86.UserProcess

theorem setcc_m8_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3) (op : BitVec 8)
    (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hw : MemWritable t lin 1) :
    (X86.Instructions.SETO_MEMb ip ctx mod rm op).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 8)
        (setccSpec (condHolds (op.extractLsb' 0 4) (StatusFlags.ofRFLAGS t.RFLAGS))) next) := by
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 8 (by decide)
    (setccSpec (condHolds (op.extractLsb' 0 4) (StatusFlags.ofRFLAGS t.RFLAGS))) hw.low
    hw.mem
  unfold X86.Instructions.SETO_MEMb
  spec_bind_rfl
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.Instructions.Operations.SETcc => setcc_operation _ _,
    Logical_Mem_Write => hwrite]

end X86Proofs
