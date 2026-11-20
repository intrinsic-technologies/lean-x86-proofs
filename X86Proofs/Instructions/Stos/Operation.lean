import X86Proofs.Program.ReadWrite.String

/-!
# One string store

`stosSpec n t`: what one `STOS` of `n` bits does with the direction flag clear: store the low `n`
bits of RAX at RDI and advance RDI by `n / 8`. The bookkeeping of the data write (oracle bits and
the `store` trace event) is `dataAccess`.
`stosDownSpec n t`: the same with the direction flag set (DF = 1), the
addresses stepping down by `n / 8` (`store_string_operation_down`).
-/

namespace X86Proofs

open X86 X86.Machine

/--
One string store of `n` bits with DF = 0, from state `t`: the low `n` bits of RAX are stored at
RDI, then RDI advances by `n / 8`.
-/
def stosSpec (n : Nat) (t : RamState) : RamState :=
  let u := (Operand.mem (rdi.read t) : Operand n).write (dataAccess t "store")
    ((Operand.reg 0 : Operand n).read t)
  rdi.write u (rdi.read t + BitVec.ofNat 64 (n / 8))

/--
One string store of `n` bits with DF = 1, from state `t`: the low `n` bits of RAX are stored at
RDI, then RDI goes back by `n / 8`.
-/
def stosDownSpec (n : Nat) (t : RamState) : RamState :=
  let u := (Operand.mem (rdi.read t) : Operand n).write (dataAccess t "store")
    ((Operand.reg 0 : Operand n).read t)
  rdi.write u (rdi.read t - BitVec.ofNat 64 (n / 8))

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem store_string_operation [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (ctx : Instruction_Context) (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hw : MemWritable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Operations.STORE_STRING 64 n ctx).run t = (.ok (), stosSpec n t) := by
  have hwrite : (Logical_Mem_Write (size := n) (nullDataSegment t.ES) (rdi.read t)
      ((Operand.reg 0 : Operand n).read t) .Normal_Alignment false false .Memory_Type_Unknown
      false).run t = (.ok (), (Operand.mem (rdi.read t) : Operand n).write (dataAccess t "store")
        ((Operand.reg 0 : Operand n).read t)) := by
    rw [hes]
    exact logicalMemWrite_run t h false (rdi.read t) n hn _ hw.low hw.mem
  unfold X86.Instructions.Operations.STORE_STRING
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ (rax_run _)).trans ?_
    refine (specM_bind_run _ _ (checkedSliceRead_zero_run _ _ _ (by decide) (by decide))).trans ?_
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact hdf
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (rdiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [stosSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess]
    rfl

theorem store_string_operation_down [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (ctx : Instruction_Context) (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hw : MemWritable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Operations.STORE_STRING 64 n ctx).run t = (.ok (), stosDownSpec n t) := by
  have hwrite : (Logical_Mem_Write (size := n) (nullDataSegment t.ES) (rdi.read t)
      ((Operand.reg 0 : Operand n).read t) .Normal_Alignment false false .Memory_Type_Unknown
      false).run t = (.ok (), (Operand.mem (rdi.read t) : Operand n).write (dataAccess t "store")
        ((Operand.reg 0 : Operand n).read t)) := by
    rw [hes]
    exact logicalMemWrite_run t h false (rdi.read t) n hn _ hw.low hw.mem
  unfold X86.Instructions.Operations.STORE_STRING
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ (rax_run _)).trans ?_
    refine (specM_bind_run _ _ (checkedSliceRead_zero_run _ _ _ (by decide) (by decide))).trans ?_
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlagSet_run _ ?_)).trans ?_
    · exact hdf
    simp (config := { decide := true }) only [↓reduceIte]
    refine (specM_bind_run _ _ (rdiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (writeRDI64_run _ _).trans ?_
    simp only [stosDownSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess,
      ofInt_neg_div8, ← BitVec.sub_eq_add_neg]

theorem store_string_operation_a32 [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (ctx : Instruction_Context) (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hw : MemWritable t (rdi.read t) (n / 8))
    (hlt : (rdi.read t).toNat + n / 8 < 2^32) :
    (X86.Instructions.Operations.STORE_STRING 32 n ctx).run t = (.ok (), stosSpec n t) := by
  have hwrite : (Logical_Mem_Write (size := n) (nullDataSegment t.ES) (rdi.read t)
      ((Operand.reg 0 : Operand n).read t) .Normal_Alignment false false .Memory_Type_Unknown
      false).run t = (.ok (), (Operand.mem (rdi.read t) : Operand n).write (dataAccess t "store")
        ((Operand.reg 0 : Operand n).read t)) := by
    rw [hes]
    exact logicalMemWrite_run t h false (rdi.read t) n hn _ hw.low hw.mem
  have ha : ((rdi.read t).setWidth 32).setWidth 64 = rdi.read t :=
    setWidth32_setWidth64_of_lt (by omega)
  unfold X86.Instructions.Operations.STORE_STRING
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ (rax_run _)).trans ?_
    refine (specM_bind_run _ _ (checkedSliceRead_zero_run _ _ _ (by decide) (by decide))).trans ?_
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rdiSlice32_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend32_run _ _)).trans ?_
    rw [ha]
    refine (specM_bind_run _ _ hwrite).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact hdf
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (rdiSlice32_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt32_run _ _ _)).trans ?_
    refine (writeRDI32_run _ _).trans ?_
    simp only [stosSpec, Operand.read_reg_write_mem, Operand.read_reg_dataAccess, ofInt32_div8]
    rw [setWidth64_add_of_lt (by omega)]

end X86Proofs
