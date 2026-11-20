import X86Proofs.Step.Selector
import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.MovSreg.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_m16_sreg_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (hreg : reg.toNat < 6)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hw : MemWritable t lin 2) :
    (X86.Instructions.MOV_MEMw_SEG ip ctx mod reg rm).run s =
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 16)
        (movsregSpec 16 (segSelector t reg)) next) := by
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 16 (by decide)
    (movsregSpec 16 (segSelector t reg)) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMw_SEG
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_bind_with (liftM_run_of_ok (isValidSegmentIndex_read reg hreg) _)
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  spec_run [
    Read_Segment => readSegment_run _ _ hreg,
    liftM => movsreg_operation _ 16 (by decide) _,
    Logical_Mem_Write => hwrite]

end X86Proofs
