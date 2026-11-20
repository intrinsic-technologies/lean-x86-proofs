import X86Proofs.Program.ReadWrite.String
import X86Proofs.Instructions.Cmp.Operation
import X86Proofs.Instructions.Branch.Cond

/-!
# One string scan

`scasSpec n t`: what one `SCAS` of `n` bits does with the direction flag clear: compare the low `n`
bits of RAX with the `n`-bit memory operand at RDI as `CMP` does (the flags of the subtraction,
`cmpSpec`), and advance RDI by `n / 8`. The bookkeeping of the data read (oracle bits and the
`load` trace event) is `dataAccess`. `repeScasSpec` and `repneScasSpec`: one iteration of `REPE
SCAS` (going on while the operands are equal) and `REPNE SCAS` (while they differ).
`scasDownSpec n t`: the same with the direction flag set (DF = 1), the
addresses stepping down by `n / 8` (`scan_string_operation_down`).
-/

namespace X86Proofs

open X86 X86.Machine

/--
One string scan of `n` bits with DF = 0, from state `t`: RDI advances by `n / 8`, and the status
flags are those of `cmp` of the low `n` bits of RAX with the `n`-bit value at RDI.
-/
def scasSpec (n : Nat) (t : RamState) : RamState :=
  let u := rdi.write (dataAccess t "load") (rdi.read t + BitVec.ofNat 64 (n / 8))
  setFlags u (cmpSpec ((Operand.reg 0 : Operand n).read t)
    ((Operand.mem (rdi.read t) : Operand n).read t))

/--
One string scan of `n` bits with DF = 1, from state `t`: RDI goes back by `n / 8`, and the status
flags are those of `cmp` of the low `n` bits of RAX with the `n`-bit value at RDI.
-/
def scasDownSpec (n : Nat) (t : RamState) : RamState :=
  let u := rdi.write (dataAccess t "load") (rdi.read t - BitVec.ofNat 64 (n / 8))
  setFlags u (cmpSpec ((Operand.reg 0 : Operand n).read t)
    ((Operand.mem (rdi.read t) : Operand n).read t))

/-- Whether `REPE SCAS` of `n` bits goes on after the scan at `t`: RCX - 1 is not zero and the low
`n` bits of RAX equal the operand at RDI (ZF). -/
def repeScasCont (n : Nat) (t : RamState) : Bool :=
  !(rcx.read t - 1 == 0#64) &&
    (cmpSpec ((Operand.reg 0 : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).ZF

/--
One iteration of `REPE SCAS` of `n` bits with DF = 0 and RCX ≠ 0, from state `t`: one string scan
(`scasSpec`) and RCX decremented; if the instruction goes on (`repeScasCont`), the repeat flag
(`Repeat_String_Operation`) is
set and the flags are put back as they were.
-/
def repeScasSpec (n : Nat) (t : RamState) : RamState :=
  if repeScasCont n t then
    { rcx.write (scasSpec n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (scasSpec n t) (rcx.read t - 1) with Repeat_String_Operation := false }

/-- Whether `REPNE SCAS` of `n` bits goes on after the scan at `t`: RCX - 1 is not zero and the low
`n` bits of RAX differ from the operand at RDI (ZF clear). -/
def repneScasCont (n : Nat) (t : RamState) : Bool :=
  !(rcx.read t - 1 == 0#64) &&
    !(cmpSpec ((Operand.reg 0 : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).ZF

/--
One iteration of `REPNE SCAS` of `n` bits with DF = 0 and RCX ≠ 0, from state `t`: one string scan
(`scasSpec`) and RCX decremented; if the instruction goes on (`repneScasCont`), the repeat flag
(`Repeat_String_Operation`) is
set and the flags are put back as they were.
-/
def repneScasSpec (n : Nat) (t : RamState) : RamState :=
  if repneScasCont n t then
    { rcx.write (scasSpec n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (scasSpec n t) (rcx.read t - 1) with Repeat_String_Operation := false }

/-- `repeScasSpec` with DF = 1: one string scan stepping down (`scasDownSpec`). -/
def repeScasDownSpec (n : Nat) (t : RamState) : RamState :=
  if repeScasCont n t then
    { rcx.write (scasDownSpec n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (scasDownSpec n t) (rcx.read t - 1) with Repeat_String_Operation := false }

/-- `repneScasSpec` with DF = 1: one string scan stepping down (`scasDownSpec`). -/
def repneScasDownSpec (n : Nat) (t : RamState) : RamState :=
  if repneScasCont n t then
    { rcx.write (scasDownSpec n t) (rcx.read t - 1) with
      Repeat_String_Operation := true, RFLAGS := t.RFLAGS }
  else { rcx.write (scasDownSpec n t) (rcx.read t - 1) with Repeat_String_Operation := false }

/-- `repeScasSpec` does not read the repeat flag (`Repeat_String_Operation`) it starts from (it sets
it). -/
theorem repeScasSpec_setRepeat (n : Nat) (t : RamState) (b : Bool) :
    repeScasSpec n { t with Repeat_String_Operation := b } = repeScasSpec n t := rfl

/-- `repneScasSpec` does not read the repeat flag (`Repeat_String_Operation`) it starts from. -/
theorem repneScasSpec_setRepeat (n : Nat) (t : RamState) (b : Bool) :
    repneScasSpec n { t with Repeat_String_Operation := b } = repneScasSpec n t := rfl

/-- `repeScasDownSpec` does not read the repeat flag (`Repeat_String_Operation`) it starts from. -/
theorem repeScasDownSpec_setRepeat (n : Nat) (t : RamState) (b : Bool) :
    repeScasDownSpec n { t with Repeat_String_Operation := b } = repeScasDownSpec n t := rfl

/-- `repneScasDownSpec` does not read the repeat flag (`Repeat_String_Operation`) it starts from. -/
theorem repneScasDownSpec_setRepeat (n : Nat) (t : RamState) (b : Bool) :
    repneScasDownSpec n { t with Repeat_String_Operation := b } = repneScasDownSpec n t := rfl

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem scan_string_operation [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (ctx : Instruction_Context) (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hr : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Operations.SCAN_STRING 64 n ctx).run t = (.ok (), scasSpec n t) := by
  have hread : (Logical_Mem_Read (nullDataSegment t.ES) (rdi.read t) n .Memory_Read
      .Normal_Alignment false).run t =
      (.ok ((Operand.mem (rdi.read t) : Operand n).read t), dataAccess t "load") := by
    rw [hes]
    exact logicalMemRead_run t h false (rdi.read t) n hn .Memory_Read (.inl rfl) hr.low hr.mem
  have hcmp := fun (u : RamState) (x y : BitVec n) => cmp_flags_run u n hn x y
  unfold X86.Instructions.Operations.SCAN_STRING
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rax_run _)).trans ?_
    refine (specM_bind_run _ _ (checkedSliceRead_zero_run _ _ _ (by decide) (by decide))).trans ?_
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact hdf
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (rdiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRDI64_run _ _)).trans ?_
    refine (hcmp _ _ _).trans ?_
    simp only [scasSpec, Operand.read_reg_dataAccess, ofInt_div8]
    rfl

theorem rcx_read_scasSpec (n : Nat) (t : RamState) : rcx.read (scasSpec n t) = rcx.read t := by
  simp only [scasSpec]
  rw [Operand.read_setFlags, Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_reg_dataAccess]

open scoped X86.Runtime.Syntax in
theorem repeScas_cond (n : Nat) (t : RamState) :
    ((!(rcx.read (rcx.write (scasSpec n t) (rcx.read t - 1)) == 0#64)) &&&
      (BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (scasSpec n t) (rcx.read t - 1)).RFLAGS == 1)) =
      repeScasCont n t := by
  have hf : (scasSpec n t).RFLAGS = (cmpSpec ((Operand.reg 0 : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := rfl
  have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
    extractLsb'_one_beq r 6
  rw [rcx_read_write, show (rcx.write (scasSpec n t) (rcx.read t - 1)).RFLAGS =
      (scasSpec n t).RFLAGS from rfl, show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl,
    hb, hf]
  unfold repeScasCont
  rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t.RFLAGS]
  show _ = (!(rcx.read t - 1 == 0#64) && (StatusFlags.store _ t.RFLAGS).getLsbD 6)
  cases (rcx.read t - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]

open scoped X86.Runtime.Syntax in
theorem repe_scan_after (n : Nat) (u : RamState) (b : Bool) :
    (do
      let x ← X86.Runtime.liftTotal RCX
      let v ← X86.Runtime.CheckedSlice.read x 0 64
      let z ← liftM (Std.Bits.Is_Zero (size := 64) v)
      let zf ← X86.Runtime.liftTotal RFLAGS.ZF
      X86.Runtime.liftTotal (Repeat_String_Operation.assign ((!z) &&& (zf == 1)))
      let w ← get
      if w.Repeat_String_Operation = true then
        modify fun x : RamState => { x with RFLAGS := u.RFLAGS }
      else pure () : X86.Runtime.PartialSpecM X86.Exception RamState Unit).run
      { rcx.write (scasSpec n u) (rcx.read (scasSpec n u) - 1) with
        Repeat_String_Operation := b } =
      some (.ok (), repeScasSpec n u) := by
  rw [rcx_read_scasSpec]
  have hslice (w : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run w = some (.ok x, w) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
    partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  have hC := repeScas_cond n u
  simp only [Operand.read_reg_of_gpr_eq (show ({ rcx.write (scasSpec n u)
    (rcx.read u - 1) with Repeat_String_Operation := b } : RamState).GPR =
    (rcx.write (scasSpec n u) (rcx.read u - 1)).GPR from rfl)]
  rw [hC]
  unfold repeScasSpec
  split
  · rename_i hc
    rw [hc]
    rfl
  · rename_i hc
    rw [Bool.not_eq_true] at hc
    rw [hc]
    rfl

open scoped X86.Runtime.Syntax in
theorem repneScas_cond (n : Nat) (t : RamState) :
    ((!(rcx.read (rcx.write (scasSpec n t) (rcx.read t - 1)) == 0#64)) &&&
      (BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (scasSpec n t) (rcx.read t - 1)).RFLAGS == 0)) =
      repneScasCont n t := by
  have hf : (scasSpec n t).RFLAGS = (cmpSpec ((Operand.reg 0 : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := rfl
  have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 0) = !r.getLsbD 6 := by
    rw [← extractLsb'_one_beq r 6]
    generalize BitVec.extractLsb' 6 1 r = x
    revert x
    decide
  rw [rcx_read_write, show (rcx.write (scasSpec n t) (rcx.read t - 1)).RFLAGS =
      (scasSpec n t).RFLAGS from rfl, show Int.toNat 6 = 6 from rfl, show Int.toNat 1 = 1 from rfl,
    hb, hf]
  unfold repneScasCont
  rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t.RFLAGS]
  show _ = (!(rcx.read t - 1 == 0#64) && !(StatusFlags.store _ t.RFLAGS).getLsbD 6)
  cases (rcx.read t - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]

open scoped X86.Runtime.Syntax in
theorem repne_scan_after (n : Nat) (u : RamState) (b : Bool) :
    (do
      let x ← X86.Runtime.liftTotal RCX
      let v ← X86.Runtime.CheckedSlice.read x 0 64
      let z ← liftM (Std.Bits.Is_Zero (size := 64) v)
      let zf ← X86.Runtime.liftTotal RFLAGS.ZF
      X86.Runtime.liftTotal (Repeat_String_Operation.assign ((!z) &&& (zf == 0)))
      let w ← get
      if w.Repeat_String_Operation = true then
        modify fun x : RamState => { x with RFLAGS := u.RFLAGS }
      else pure () : X86.Runtime.PartialSpecM X86.Exception RamState Unit).run
      { rcx.write (scasSpec n u) (rcx.read (scasSpec n u) - 1) with
        Repeat_String_Operation := b } =
      some (.ok (), repneScasSpec n u) := by
  rw [rcx_read_scasSpec]
  have hslice (w : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run w = some (.ok x, w) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
    partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  have hC := repneScas_cond n u
  simp only [Operand.read_reg_of_gpr_eq (show ({ rcx.write (scasSpec n u)
    (rcx.read u - 1) with Repeat_String_Operation := b } : RamState).GPR =
    (rcx.write (scasSpec n u) (rcx.read u - 1)).GPR from rfl)]
  rw [hC]
  unfold repneScasSpec
  split
  · rename_i hc
    rw [hc]
    rfl
  · rename_i hc
    rw [Bool.not_eq_true] at hc
    rw [hc]
    rfl

theorem scan_string_operation_down [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (ctx : Instruction_Context) (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hr : MemReadable t (rdi.read t) (n / 8)) :
    (X86.Instructions.Operations.SCAN_STRING 64 n ctx).run t = (.ok (), scasDownSpec n t) := by
  have hread : (Logical_Mem_Read (nullDataSegment t.ES) (rdi.read t) n .Memory_Read
      .Normal_Alignment false).run t =
      (.ok ((Operand.mem (rdi.read t) : Operand n).read t), dataAccess t "load") := by
    rw [hes]
    exact logicalMemRead_run t h false (rdi.read t) n hn .Memory_Read (.inl rfl) hr.low hr.mem
  have hcmp := fun (u : RamState) (x y : BitVec n) => cmp_flags_run u n hn x y
  unfold X86.Instructions.Operations.SCAN_STRING
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rdiSlice_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
    refine (specM_bind_run _ _ (rax_run _)).trans ?_
    refine (specM_bind_run _ _ (checkedSliceRead_zero_run _ _ _ (by decide) (by decide))).trans ?_
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlagSet_run _ ?_)).trans ?_
    · exact hdf
    simp (config := { decide := true }) only [↓reduceIte]
    refine (specM_bind_run _ _ (rdiSlice_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRDI64_run _ _)).trans ?_
    refine (hcmp _ _ _).trans ?_
    simp only [scasDownSpec, Operand.read_reg_dataAccess, ofInt_neg_div8, ← BitVec.sub_eq_add_neg]
    rfl

theorem scan_string_operation_a32 [Bindings] (t : RamState) (h : DataReady t)
    (hmode : In64BitMode t) (n : Nat) (hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (ctx : Instruction_Context) (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hr : MemReadable t (rdi.read t) (n / 8))
    (hlt : (rdi.read t).toNat + n / 8 < 2^32) :
    (X86.Instructions.Operations.SCAN_STRING 32 n ctx).run t = (.ok (), scasSpec n t) := by
  have hread : (Logical_Mem_Read (nullDataSegment t.ES) (rdi.read t) n .Memory_Read
      .Normal_Alignment false).run t =
      (.ok ((Operand.mem (rdi.read t) : Operand n).read t), dataAccess t "load") := by
    rw [hes]
    exact logicalMemRead_run t h false (rdi.read t) n hn .Memory_Read (.inl rfl) hr.low hr.mem
  have hcmp := fun (u : RamState) (x y : BitVec n) => cmp_flags_run u n hn x y
  have ha : ((rdi.read t).setWidth 32).setWidth 64 = rdi.read t :=
    setWidth32_setWidth64_of_lt (by omega)
  unfold X86.Instructions.Operations.SCAN_STRING
  rcases hn with rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [assert_of_true, pure_bind]
    refine (specM_bind_run _ _ hmode).trans ?_
    simp only [↓reduceIte]
    rw [specM_bind_run _ _ (get_run t)]
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (rdiSlice32_run t)).trans ?_
    refine (specM_bind_run _ _ (zeroExtend32_run _ _)).trans ?_
    rw [ha]
    refine (specM_bind_run _ _ (rax_run _)).trans ?_
    refine (specM_bind_run _ _ (checkedSliceRead_zero_run _ _ _ (by decide) (by decide))).trans ?_
    refine (specM_bind_run _ _ hread).trans ?_
    refine (specM_bind_run _ _ rfl).trans ?_
    refine (specM_bind_run _ _ (directionFlag_run _ ?_)).trans ?_
    · exact hdf
    simp only [beq_self_eq_true, ↓reduceIte]
    refine (specM_bind_run _ _ (rdiSlice32_run _)).trans ?_
    refine (specM_bind_run _ _ (addInt32_run _ _ _)).trans ?_
    refine (specM_bind_run _ _ (writeRDI32_run _ _)).trans ?_
    refine (hcmp _ _ _).trans ?_
    simp only [scasSpec, Operand.read_reg_dataAccess, ofInt32_div8]
    rw [setWidth64_add_of_lt (by omega)]
    rfl

open scoped X86.Runtime.Syntax in
theorem repe_scan_after_a32 (n : Nat) (u : RamState) (hcl : (rcx.read u).toNat < 2^32)
    (h0 : rcx.read u ≠ 0) (b : Bool) :
    (do
      let x ← X86.Runtime.liftTotal RCX
      let v ← X86.Runtime.CheckedSlice.read x 0 32
      let z ← liftM (Std.Bits.Is_Zero (size := 32) v)
      let zf ← X86.Runtime.liftTotal RFLAGS.ZF
      X86.Runtime.liftTotal (Repeat_String_Operation.assign ((!z) &&& (zf == 1)))
      let w ← get
      if w.Repeat_String_Operation = true then
        modify fun x : RamState => { x with RFLAGS := u.RFLAGS }
      else pure () : X86.Runtime.PartialSpecM X86.Exception RamState Unit).run
      { rcx.write (scasSpec n u) (((rcx.read (scasSpec n u)).setWidth 32 - 1).setWidth 64) with
        Repeat_String_Operation := b } =
      some (.ok (), repeScasSpec n u) := by
  have hC : ((!(rcx.read u - 1 == 0#64)) &&&
      (BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (scasSpec n u) (rcx.read u - 1)).RFLAGS == 1)) = repeScasCont n u := by
    have := repeScas_cond n u
    rwa [rcx_read_write] at this
  have hz : ((rcx.read u - 1).setWidth 32 == 0#32) = (rcx.read u - 1 == 0#64) :=
    setWidth32_beq_zero_of_lt (toNat_sub_one_lt_of_lt hcl h0)
  rw [rcx_read_scasSpec, setWidth64_sub_one_of_lt hcl h0]
  have hslice (w : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run w =
        some (.ok (x.setWidth 32), w) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
    partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  simp only [Operand.read_reg_of_gpr_eq (show ({ rcx.write (scasSpec n u)
    (rcx.read u - 1) with Repeat_String_Operation := b } : RamState).GPR =
    (rcx.write (scasSpec n u) (rcx.read u - 1)).GPR from rfl)]
  rw [rcx_read_write, hz, hC]
  unfold repeScasSpec
  split
  · rename_i hc
    rw [hc]
    rfl
  · rename_i hc
    rw [Bool.not_eq_true] at hc
    rw [hc]
    rfl

open scoped X86.Runtime.Syntax in
theorem repne_scan_after_a32 (n : Nat) (u : RamState) (hcl : (rcx.read u).toNat < 2^32)
    (h0 : rcx.read u ≠ 0) (b : Bool) :
    (do
      let x ← X86.Runtime.liftTotal RCX
      let v ← X86.Runtime.CheckedSlice.read x 0 32
      let z ← liftM (Std.Bits.Is_Zero (size := 32) v)
      let zf ← X86.Runtime.liftTotal RFLAGS.ZF
      X86.Runtime.liftTotal (Repeat_String_Operation.assign ((!z) &&& (zf == 0)))
      let w ← get
      if w.Repeat_String_Operation = true then
        modify fun x : RamState => { x with RFLAGS := u.RFLAGS }
      else pure () : X86.Runtime.PartialSpecM X86.Exception RamState Unit).run
      { rcx.write (scasSpec n u) (((rcx.read (scasSpec n u)).setWidth 32 - 1).setWidth 64) with
        Repeat_String_Operation := b } =
      some (.ok (), repneScasSpec n u) := by
  have hC : ((!(rcx.read u - 1 == 0#64)) &&&
      (BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (scasSpec n u) (rcx.read u - 1)).RFLAGS == 0)) = repneScasCont n u := by
    have := repneScas_cond n u
    rwa [rcx_read_write] at this
  have hz : ((rcx.read u - 1).setWidth 32 == 0#32) = (rcx.read u - 1 == 0#64) :=
    setWidth32_beq_zero_of_lt (toNat_sub_one_lt_of_lt hcl h0)
  rw [rcx_read_scasSpec, setWidth64_sub_one_of_lt hcl h0]
  have hslice (w : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 32 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 32)).run w =
        some (.ok (x.setWidth 32), w) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, BitVec.setWidth_eq_extractLsb']
  have hzero (a : RamState) (v : BitVec 32) :
      (liftM (Std.Bits.Is_Zero (size := 32) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#32), a) :=
    rfl
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
    partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  simp only [Operand.read_reg_of_gpr_eq (show ({ rcx.write (scasSpec n u)
    (rcx.read u - 1) with Repeat_String_Operation := b } : RamState).GPR =
    (rcx.write (scasSpec n u) (rcx.read u - 1)).GPR from rfl)]
  rw [rcx_read_write, hz, hC]
  unfold repneScasSpec
  split
  · rename_i hc
    rw [hc]
    rfl
  · rename_i hc
    rw [Bool.not_eq_true] at hc
    rw [hc]
    rfl

theorem rcx_read_scasDownSpec (n : Nat) (t : RamState) :
    rcx.read (scasDownSpec n t) = rcx.read t := by
  simp only [scasDownSpec]
  rw [Operand.read_setFlags, Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_reg_dataAccess]

open scoped X86.Runtime.Syntax in
theorem repeScasDown_cond (n : Nat) (t : RamState) :
    ((!(rcx.read (rcx.write (scasDownSpec n t) (rcx.read t - 1)) == 0#64)) &&&
      (BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (scasDownSpec n t) (rcx.read t - 1)).RFLAGS == 1)) =
      repeScasCont n t := by
  have hf : (scasDownSpec n t).RFLAGS = (cmpSpec ((Operand.reg 0 : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := rfl
  have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 1) = r.getLsbD 6 :=
    extractLsb'_one_beq r 6
  rw [rcx_read_write, show (rcx.write (scasDownSpec n t) (rcx.read t - 1)).RFLAGS =
      (scasDownSpec n t).RFLAGS from rfl, show Int.toNat 6 = 6 from rfl,
    show Int.toNat 1 = 1 from rfl,
    hb, hf]
  unfold repeScasCont
  rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t.RFLAGS]
  show _ = (!(rcx.read t - 1 == 0#64) && (StatusFlags.store _ t.RFLAGS).getLsbD 6)
  cases (rcx.read t - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]

open scoped X86.Runtime.Syntax in
theorem repe_scan_after_down (n : Nat) (u : RamState) (b : Bool) :
    (do
      let x ← X86.Runtime.liftTotal RCX
      let v ← X86.Runtime.CheckedSlice.read x 0 64
      let z ← liftM (Std.Bits.Is_Zero (size := 64) v)
      let zf ← X86.Runtime.liftTotal RFLAGS.ZF
      X86.Runtime.liftTotal (Repeat_String_Operation.assign ((!z) &&& (zf == 1)))
      let w ← get
      if w.Repeat_String_Operation = true then
        modify fun x : RamState => { x with RFLAGS := u.RFLAGS }
      else pure () : X86.Runtime.PartialSpecM X86.Exception RamState Unit).run
      { rcx.write (scasDownSpec n u) (rcx.read (scasDownSpec n u) - 1) with
        Repeat_String_Operation := b } =
      some (.ok (), repeScasDownSpec n u) := by
  rw [rcx_read_scasDownSpec]
  have hslice (w : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run w = some (.ok x, w) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
    partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  have hC := repeScasDown_cond n u
  simp only [Operand.read_reg_of_gpr_eq (show ({ rcx.write (scasDownSpec n u)
    (rcx.read u - 1) with Repeat_String_Operation := b } : RamState).GPR =
    (rcx.write (scasDownSpec n u) (rcx.read u - 1)).GPR from rfl)]
  rw [hC]
  unfold repeScasDownSpec
  split
  · rename_i hc
    rw [hc]
    rfl
  · rename_i hc
    rw [Bool.not_eq_true] at hc
    rw [hc]
    rfl

open scoped X86.Runtime.Syntax in
theorem repneScasDown_cond (n : Nat) (t : RamState) :
    ((!(rcx.read (rcx.write (scasDownSpec n t) (rcx.read t - 1)) == 0#64)) &&&
      (BitVec.extractLsb' (Int.toNat 6) (Int.toNat 1)
        (rcx.write (scasDownSpec n t) (rcx.read t - 1)).RFLAGS == 0)) =
      repneScasCont n t := by
  have hf : (scasDownSpec n t).RFLAGS = (cmpSpec ((Operand.reg 0 : Operand n).read t)
      ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := rfl
  have hb (r : BitVec 64) : (BitVec.extractLsb' 6 1 r == 0) = !r.getLsbD 6 := by
    rw [← extractLsb'_one_beq r 6]
    generalize BitVec.extractLsb' 6 1 r = x
    revert x
    decide
  rw [rcx_read_write, show (rcx.write (scasDownSpec n t) (rcx.read t - 1)).RFLAGS =
      (scasDownSpec n t).RFLAGS from rfl, show Int.toNat 6 = 6 from rfl,
    show Int.toNat 1 = 1 from rfl,
    hb, hf]
  unfold repneScasCont
  rw [← StatusFlags.ofRFLAGS_store (cmpSpec _ _) t.RFLAGS]
  show _ = (!(rcx.read t - 1 == 0#64) && !(StatusFlags.store _ t.RFLAGS).getLsbD 6)
  cases (rcx.read t - 1 == 0#64) <;> simp [HAnd.hAnd, AndOp.and, strictAnd]

open scoped X86.Runtime.Syntax in
theorem repne_scan_after_down (n : Nat) (u : RamState) (b : Bool) :
    (do
      let x ← X86.Runtime.liftTotal RCX
      let v ← X86.Runtime.CheckedSlice.read x 0 64
      let z ← liftM (Std.Bits.Is_Zero (size := 64) v)
      let zf ← X86.Runtime.liftTotal RFLAGS.ZF
      X86.Runtime.liftTotal (Repeat_String_Operation.assign ((!z) &&& (zf == 0)))
      let w ← get
      if w.Repeat_String_Operation = true then
        modify fun x : RamState => { x with RFLAGS := u.RFLAGS }
      else pure () : X86.Runtime.PartialSpecM X86.Exception RamState Unit).run
      { rcx.write (scasDownSpec n u) (rcx.read (scasDownSpec n u) - 1) with
        Repeat_String_Operation := b } =
      some (.ok (), repneScasDownSpec n u) := by
  rw [rcx_read_scasDownSpec]
  have hslice (w : RamState) (x : BitVec 64) : (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.PartialSpecM X86.Exception RamState (BitVec 64)).run w = some (.ok x, w) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  have hzero (a : RamState) (v : BitVec 64) :
      (liftM (Std.Bits.Is_Zero (size := 64) v) :
        X86.Runtime.PartialSpecM X86.Exception RamState Bool).run a = some (.ok (v == 0#64), a) :=
    rfl
  rw [partialSpecM_liftTotal_bind_run _ _ (rcx_run _), partialSpecM_bind_run _ _ (hslice _ _),
    partialSpecM_bind_run _ _ (hzero _ _)]
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  refine (partialSpecM_liftTotal_bind_run _ _ rfl).trans ?_
  rw [partialSpecM_get_bind_run]
  have hC := repneScasDown_cond n u
  simp only [Operand.read_reg_of_gpr_eq (show ({ rcx.write (scasDownSpec n u)
    (rcx.read u - 1) with Repeat_String_Operation := b } : RamState).GPR =
    (rcx.write (scasDownSpec n u) (rcx.read u - 1)).GPR from rfl)]
  rw [hC]
  unfold repneScasDownSpec
  split
  · rename_i hc
    rw [hc]
    rfl
  · rename_i hc
    rw [Bool.not_eq_true] at hc
    rw [hc]
    rfl

end X86Proofs
