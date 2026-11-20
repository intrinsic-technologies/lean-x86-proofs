import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Step.Address

/-!
# Table look-up translation

`xlatSpec t`: what `XLAT` does with 64-bit addresses: AL becomes the byte at `xlatAddr t`, RBX
plus AL zero-extended (the bits of RAX above AL kept). The bookkeeping of the data read (oracle
bits and the `load` trace event) is `dataAccess`. lean-x86's `Operations.XLAT` takes the address
size and the segment the form found (`xlat_operation`: 64 bits, the flat data segment).
-/

namespace X86Proofs

open X86 X86.Machine

/-- The address `XLAT` reads in `s`: RBX plus AL, unsigned, wrapping at 64 bits. -/
def xlatAddr (s : RamState) : BitVec 64 :=
  rbx.read s + ((Operand.reg 0 : Operand 8).read s).setWidth 64

/-- `XLAT` from state `t`: the byte at `xlatAddr t` written to AL. -/
def xlatSpec (t : RamState) : RamState :=
  (Operand.reg 0 : Operand 8).write (dataAccess t "load")
    ((Operand.mem (xlatAddr t) : Operand 8).read t)

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem xlat_operation [Bindings] (t : RamState) (h : DataReady t)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hr : MemReadable t (xlatAddr t) 1) :
    (X86.Instructions.Operations.XLAT 64 (nullDataSegment t.DS)).run t = (.ok (), xlatSpec t) := by
  have hread : (Logical_Mem_Read (nullDataSegment t.DS) (xlatAddr t) 8 .Memory_Read
      .Normal_Alignment false).run t =
      (.ok ((Operand.mem (xlatAddr t) : Operand 8).read t), dataAccess t "load") := by
    rw [hds]
    exact logicalMemRead_run t h false (xlatAddr t) 8 (by decide) .Memory_Read (.inl rfl) hr.low
      hr.mem
  unfold X86.Instructions.Operations.XLAT
  simp only [assert_of_true (show ((64 : Int) == 16 || (64 : Int) == 32 || (64 : Int) == 64) = true
      from rfl),
    assert_of_true (show decide ((64 : Int) ≤ 64) = true from rfl), pure_bind, bind_assoc,
    stdZeroExtend_eq_pure (n := 8) (target := 64) _ (by decide),
    stdZeroExtend_eq_pure (n := 64) (target := 64) _ (by decide)]
  refine (specM_bind_run _ _ (rbx_run t)).trans ?_
  refine (specM_bind_run _ _ (checkedSliceRead_zero_run t _ 64 (by decide) (by decide))).trans ?_
  refine (specM_bind_run _ _ (al_run t)).trans ?_
  have haddr : BitVec.setWidth (Int.toNat 64) (BitVec.setWidth (Int.toNat 64) t.GPR[gprIndex 3] +
      BitVec.setWidth (Int.toNat 64) (BitVec.setWidth 8 t.GPR[gprIndex 0])) = xlatAddr t := by
    simp [xlatAddr, Operand.read]
  rw [haddr]
  refine (specM_bind_run _ _ hread).trans ?_
  exact (alWrite_run _ _).trans rfl

end X86Proofs
