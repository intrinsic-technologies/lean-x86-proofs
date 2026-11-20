import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Rmw
import X86Proofs.Instructions.Cmpxchg8b.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmpxchg8b_lock_m64_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = asz) (hw : ctx.rex_w = 0)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin) (ht : DataReady t)
    (hlow : lin.toNat + 8 ≤ 2^32)
    (hmem : ∀ i, i < 8 → (t.external[lin + BitVec.ofNat 64 i]?).isSome)
    (hlk : LockReady t lin 8) :
    (X86.Instructions.CMPXCHG8B_LOCK_MEMq_1 ip ctx mod rm).run s =
      let x := (Operand.mem lin : Operand 64).read t
      let acc := concat32 ((Operand.reg 2 : Operand 64).read t)
        ((Operand.reg 0 : Operand 64).read t)
      let rep := concat32 ((Operand.reg 1 : Operand 64).read t)
        ((Operand.reg 3 : Operand 64).read t)
      let out := cmpxchg8bSpec (StatusFlags.ofRFLAGS t.RFLAGS) acc rep x
      (.ok (), if acc = x then writeRmwOutputs t lin out 0 next
        else
          writeRmwRegPairOutputs t lin out 0 next 2 (x.extractLsb' 32 32) 0 (x.setWidth 32)) := by
  have hcontext : {ctx with address_size := asz, rex_w := 0} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg_lock t ht seg addr lin hseg 64 (by decide) hlow hmem hlk
  have hwrite (u : RamState) (hu : DataReady u) (he : u.external = t.external) (v : BitVec 64) :=
    logicalMemWrite_run_seg_lock u hu seg addr lin hseg 64 (by decide) v hlow
      (by rw [he]; exact hmem)
  have hd (u : RamState) (hst : SameControls t u) (hcs : u.CS = t.CS) (hcr3 : u.CR3 = t.CR3)
      (hefer : u.IA32_EFER = t.IA32_EFER) (hcpl : u.CPL = t.CPL) (hdr7 : u.DR7 = t.DR7)
      (he : u.external = t.external) : DataReady u :=
    ht.of_sameControls hst hcs hcr3 hefer hcpl hdr7 (he ▸ ht.tables)
  unfold X86.Instructions.CMPXCHG8B_LOCK_MEMq_1
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  simp only [Operand.read_reg64]
  by_cases hc :
      concat32 t.GPR[gprIndex 2] t.GPR[gprIndex 0] = (Operand.mem lin : Operand 64).read t
  · simp only [cmpxchg8bSpec, hc, ↓reduceIte, decide_true, writeRmwOutputs, writeFlagsOutputs,
      oracleSkip_zero]
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.CMPXCHG8B => cmpxchg8b_operation_eq _ _ (by exact hc),
      Logical_Mem_Write => hwrite _
        (by exact hd _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
              rfl rfl) (by rfl) _]
  · simp only [cmpxchg8bSpec, hc, ↓reduceIte, decide_false, writeRmwRegPairOutputs,
      writeRmwOutputs, writeFlagsOutputs, oracleSkip_zero]
    spec_run [
      Logical_Mem_Read => hread,
      X86.Instructions.Operations.CMPXCHG8B => cmpxchg8b_operation_ne _ _ (by exact hc),
      Logical_Mem_Write => hwrite _
        (by exact hd _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
              rfl rfl) (by rfl) _]

end X86Proofs
