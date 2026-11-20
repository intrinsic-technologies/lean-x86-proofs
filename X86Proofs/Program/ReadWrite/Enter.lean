import X86Proofs.Program.ReadWrite.String
import X86Proofs.Step.Fetch

/-!
# ENTER at 64 bits, nesting levels 0 and 1

lean-x86's `Operations.ENTER 64 64 size level` (the `C8 iw ib` form at operand size 64): push RBP
with `Push_Stack` (the frame pointer `frame` is the new top, RSP - 8); at level 1 push `frame`
too (the loop over the saved frame pointers of the enclosing levels runs over `intRange 1 0`, no
pass); subtract the frame size (zero-extended) from the new top; check that 8 bytes at that final
RSP can be written (`Check_Logical_Address_Is_Writable`, `checkLogicalAddressIsWritable_run`,
which writes nothing); RBP := `frame`, RSP := the final top.

- `enter_operation0`, `enter_operation1`: the operation at level 0 and 1, with results
  `enterState0` and `enterState1` (`pushMem`: one `Push_Stack` write and its bookkeeping
  `stackAccess`; `enterFinish`: the check's bookkeeping `checkAccess`, then RBP and RSP).
- What a step whose form ends in them does: `afterStep_enter<l>_rip`,
  `Operand.read_afterStep_enter<l>_rsp`, `Operand.read_afterStep_enter<l>_rbp`,
  `Operand.read_afterStep_enter<l>_mem` (and `_mem2` at level 1: the 8 bytes at RSP - 16 hold the
  frame pointer), `AgreesExcept.afterStep_enter<l>` (`[.reg 4, .reg 5, .mem (RSP - 8) 8, .rip]`,
  plus `.mem (RSP - 16) 8` at level 1), `ReadyToStep.afterStep_enter<l>`.

- `Effect.avoids_of_components_enter0`, `Effect.avoids_of_components_enter1`: an effect with
  ENTER's components avoids the code if its stack bytes are apart from it.

Levels 2 to 31 (the level byte is taken modulo 32) run the loop: `L - 1` passes, pass `i` reading
the 8 bytes at RBP - 8 (i + 1) (through SS, `SegAccess.userStack`) and pushing them, then the new
frame pointer is pushed; one theorem covers them all, the level a parameter `L`:

- `enter_operationN` (the loop by `enter_forIn_run`, each pass a load and a `Push_Stack`; the state
  `enterStateN`, its copies `enterCopies`), its facts `afterStep_enterN_rip`,
  `Operand.read_afterStep_enterN_rsp`, `_rbp`, `Operand.read_afterStep_enterN_slot` (slot `k ≤ L`,
  the 8 bytes at RSP - 8 - 8 k, holds `enterSlotVal s L k`: the old RBP, the 8 bytes at
  RBP - 8 k, or the new frame pointer), `AgreesExcept.afterStep_enterN`,
  `ReadyToStep.afterStep_enterN`, `Effect.avoids_of_components_enterN`. The slots must be below
  4 GiB (so they do not wrap and are apart, `slot_apart`), and the bytes read apart from them, so
  each read sees the start state's bytes.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The bookkeeping of `Check_Logical_Address_Is_Writable`: the 464 oracle bits of
`Create_Logical_Address` (`checkLogicalAddressIsWritable_run`). -/
def checkAccess (s : RamState) : RamState := { s with oracle := oracleSkip s.oracle 464 }

/-- The state after `Push_Stack` writes the 8 bytes `v` at `a` from `t`, RSP not yet written. -/
def pushMem (t : RamState) (a v : BitVec 64) : RamState :=
  (Operand.mem a : Operand 64).write (stackAccess t) v

/-- The end of ENTER from `u`: the writability check's bookkeeping, RBP := `frame`, RSP :=
`rsp`. -/
def enterFinish (u : RamState) (frame rsp : BitVec 64) : RamState :=
  (Operand.reg 4 : Operand 64).write ((Operand.reg 5 : Operand 64).write (checkAccess u) frame) rsp

/-- The state after `ENTER size, 0` from `t`: RBP pushed at RSP - 8, RBP := RSP - 8, RSP :=
RSP - 8 - `size`. -/
def enterState0 (t : RamState) (size : BitVec 16) : RamState :=
  enterFinish (pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t)) (pushAddr t)
    (pushAddr t - size.setWidth 64)

/-- The state after `ENTER size, 1` from `t`: RBP pushed at RSP - 8, the new frame pointer
RSP - 8 pushed at RSP - 16, RBP := RSP - 8, RSP := RSP - 16 - `size`. -/
def enterState1 (t : RamState) (size : BitVec 16) : RamState :=
  enterFinish (pushMem (pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t))
      (pushAddr t - 8) (pushAddr t))
    (pushAddr t) (pushAddr t - 8 - size.setWidth 64)

@[simp] theorem pushMem_SS (t : RamState) (a v : BitVec 64) : (pushMem t a v).SS = t.SS := rfl

/-- The frame pointer read: `RBP` as a full 64-bit slice after the operand-size assertion. -/
theorem enterRbp_run (t : RamState) :
    ((do X86.Runtime.assert (decide ((64 : Int) ≤ 64))
         X86.Runtime.CheckedSlice.read (← RBP) 0 64) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run t =
      (.ok ((Operand.reg 5 : Operand 64).read t), t) := by
  rw [assert_of_true (by decide), pure_bind, specM_bind_run _ _ (rbp_run t)]
  exact checkedSliceRead_full_run t _

/-- The frame size zero-extended to 64 bits. -/
theorem zeroExtend16_run (u : RamState) (x : BitVec 16) :
    (Std.Bits.Zero_Extend (source_size := 16) x 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok (x.setWidth 64), u) := by
  simp [x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.pure]

/-- A push's write keeps the data-access facts if the bytes are outside the page tables. -/
theorem DataReady.pushMem [Bindings] {t : RamState} (h : DataReady t) {a : BitVec 64}
    (hw : MemWritable t a 8) (v : BitVec 64) : DataReady (pushMem t a v) :=
  h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
    (IdentityPageTableMemory.memStore h.tables _ _ hw.low hw.tables)

/-- Writable bytes stay writable after a push's write. -/
theorem MemWritable.pushMem {t : RamState} {a : BitVec 64} {len : Nat}
    (hw : MemWritable t a len) (b v : BitVec 64) : MemWritable (pushMem t b v) a len :=
  ⟨hw.low, fun i hi => memStore_isSome _ _ _ _ (hw.mem i hi), hw.tables⟩

/-- The state `ENTER` tests the mode in before its RSP write (RBP written, the oracle advanced by
the writability check) is in 64-bit mode if the state before those was. Stated for any state, so
that applying it does not compare the pushed states field by field. -/
theorem In64BitMode.writeRBP_oracle {u : RamState} (h : In64BitMode u)
    (o : X86.Runtime.Oracle) (v : BitVec 64) :
    In64BitMode ((Operand.reg 5 : Operand 64).write { u with oracle := o } v) :=
  h.of_cs_lma_eq rfl rfl

/-- `Operations.ENTER 64 64 size 0`: with the 8 bytes at RSP - 8 writable and the final RSP below
4 GiB, the result is `enterState0`. -/
theorem enter_operation0 [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (size : BitVec 16) (hw : MemWritable t (pushAddr t) 8)
    (hcheck : (pushAddr t - size.setWidth 64).toNat + 8 ≤ 2^32) :
    (X86.Instructions.Operations.ENTER 64 64 size 0#8).run t = (.ok (), enterState0 t size) := by
  have hw' : MemWritable t (stackPtr t - 8) 8 := hw
  have hd := h.pushMem hw ((Operand.reg 5 : Operand 64).read t)
  unfold X86.Instructions.Operations.ENTER
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (get_run t)
  spec_bind_with (rsp_run t)
  spec_bind_with (get_run t)
  spec_bind_with (enterRbp_run t)
  spec_bind_with (pushStack_run t h hss (stackPtr t) _ hw')
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (zeroExtend_full_run _ _)
  simp only [show decide (X86.Runtime.Unsigned 0#8 % 32 > 0) = false by decide,
    Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (zeroExtend16_run _ size)
  spec_bind_with (get_run _)
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (zeroExtend_full_run _ _)
  spec_bind_with (checkLogicalAddressIsWritable_run _ hd hss _ 64 (by decide) hcheck)
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (writeRBP64_run _ _)
  spec_bind_with (In64BitMode.writeRBP_oracle (in64BitMode_of_userCodeSegment hd.cs hd.efer.lma) _ _)
  exact writeRSP64_run _ _

/-- `Operations.ENTER 64 64 size 1`: with the 8 bytes at RSP - 8 and at RSP - 16 writable and the
final RSP below 4 GiB, the result is `enterState1`. -/
theorem enter_operation1 [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (size : BitVec 16) (hw : MemWritable t (pushAddr t) 8)
    (hw2 : MemWritable t (pushAddr t - 8) 8)
    (hcheck : (pushAddr t - 8 - size.setWidth 64).toNat + 8 ≤ 2^32) :
    (X86.Instructions.Operations.ENTER 64 64 size 1#8).run t = (.ok (), enterState1 t size) := by
  have hw' : MemWritable t (stackPtr t - 8) 8 := hw
  have hd := h.pushMem hw ((Operand.reg 5 : Operand 64).read t)
  have hw2' : MemWritable (pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t))
      (stackPtr t - 8 - 8) 8 := hw2.pushMem _ _
  have hd2 := hd.pushMem hw2' (pushAddr t)
  have hc := checkLogicalAddressIsWritable_run (pushMem (pushMem t (pushAddr t)
    ((Operand.reg 5 : Operand 64).read t)) (pushAddr t - 8) (pushAddr t)) hd2
    (by rw [pushMem_SS, pushMem_SS]; exact hss) (pushAddr t - 8 - size.setWidth 64) 64
    (by decide) hcheck
  unfold X86.Instructions.Operations.ENTER
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (get_run t)
  spec_bind_with (rsp_run t)
  spec_bind_with (get_run t)
  spec_bind_with (enterRbp_run t)
  spec_bind_with (pushStack_run t h hss (stackPtr t) _ hw')
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (zeroExtend_full_run _ _)
  simp only [show decide (X86.Runtime.Unsigned 1#8 % 32 > 0) = true by decide, ↓reduceIte,
    show X86.Runtime.intRange 1 (X86.Runtime.Unsigned 1#8 % 32 - 1) = [] by decide,
    List.forIn_nil]
  spec_bind_with (rbp_run _)
  spec_bind_rfl
  spec_bind_with (get_run _)
  spec_bind_with (get_run _)
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (pushStack_run _ hd hss (stackPtr t - 8) _ hw2')
  spec_bind_with (zeroExtend16_run _ size)
  spec_bind_with (get_run _)
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (zeroExtend_full_run _ _)
  spec_bind_with hc
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (writeRBP64_run _ _)
  spec_bind_with (In64BitMode.writeRBP_oracle (in64BitMode_of_userCodeSegment hd2.cs hd2.efer.lma) _ _)
  exact writeRSP64_run _ _

/-! ### Frames -/

/-- A push's bookkeeping changes nothing an effect sees. -/
theorem AgreesExcept.of_stackAccess (t : RamState) : AgreesExcept [] t (stackAccess t) :=
  ⟨fun c _ _ => by cases c <;> first | rfl | exact fun _ _ => rfl, fun _ _ => rfl,
    by simp only [fixedPart, stackAccess, beforeFetch, resetStepFields], fun _ h => h⟩

/-- The writability check's bookkeeping changes nothing an effect sees. -/
theorem AgreesExcept.of_checkAccess (t : RamState) : AgreesExcept [] t (checkAccess t) :=
  ⟨fun c _ _ => by cases c <;> first | rfl | exact fun _ _ => rfl, fun _ _ => rfl,
    by simp only [fixedPart, checkAccess, beforeFetch, resetStepFields], fun _ h => h⟩

/-- A push's write changes only its 8 bytes (besides the bookkeeping). -/
theorem AgreesExcept.of_pushMem (t : RamState) (a v : BitVec 64) :
    AgreesExcept [.mem a 8] t (pushMem t a v) :=
  (AgreesExcept.of_stackAccess t).trans (AgreesExcept.write_mem (stackAccess t) a v)

/-- The end of ENTER changes only RBP and RSP (besides the bookkeeping). -/
theorem AgreesExcept.of_enterFinish (u : RamState) (frame rsp : BitVec 64) :
    AgreesExcept [.reg 5, .reg 4] u (enterFinish u frame rsp) :=
  ((AgreesExcept.of_checkAccess u).trans (AgreesExcept.write_reg _ 5 frame)).trans
    (AgreesExcept.write_reg _ 4 rsp)

/-! ### After an `ENTER size, 0` step -/

/-- After an `ENTER size, 0` step, RIP is `nextIP`. -/
theorem afterStep_enter0_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (size : BitVec 16) (nextIP : BitVec 64) :
    (afterStep s length fun t => enterState0 { t with Next_IP := nextIP } size).RIP = nextIP := by
  simp [afterStep, finishStep, enterState0, enterFinish, checkAccess, pushMem, Operand.write,
    stackAccess, afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Memory after an `ENTER size, 0` step: RBP written at RSP - 8. -/
@[simp] theorem afterStep_enter0_external (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => enterState0 { t with Next_IP := nextIP } size).external =
      memStore s.external (pushAddr s) ((Operand.reg 5 : Operand 64).read s) := rfl

/-- After an `ENTER size, 0` step, RSP is the old RSP - 8 - `size`. -/
theorem Operand.read_afterStep_enter0_rsp (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => enterState0 { t with Next_IP := nextIP } size) =
      pushAddr s - size.setWidth 64 := by
  rw [Operand.read_afterStep, enterState0, enterFinish, Operand.read_write_reg64_self]
  rfl

/-- After an `ENTER size, 0` step, RBP is the old RSP - 8. -/
theorem Operand.read_afterStep_enter0_rbp (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.reg 5 : Operand 64).read
      (afterStep s length fun t => enterState0 { t with Next_IP := nextIP } size) =
      pushAddr s := by
  rw [Operand.read_afterStep, enterState0, enterFinish, Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_write_reg64_self]
  rfl

/-- After an `ENTER size, 0` step, the 8 bytes at the old RSP - 8 hold the old RBP. -/
theorem Operand.read_afterStep_enter0_mem (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.mem (pushAddr s) : Operand 64).read
      (afterStep s length fun t => enterState0 { t with Next_IP := nextIP } size) =
      (Operand.reg 5 : Operand 64).read s := by
  simp only [Operand.read, afterStep_enter0_external]
  exact memLoad_memStore _ _ (by decide) (by decide) _

/-- An `ENTER size, 0` step changes only RSP, RBP, the 8 bytes at RSP - 8 and RIP (besides the
bookkeeping). -/
theorem AgreesExcept.afterStep_enter0 (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    AgreesExcept [.reg 4, .reg 5, .mem (pushAddr s) 8, .rip] s
      (afterStep s length fun t => enterState0 { t with Next_IP := nextIP } size) :=
  (((AgreesExcept.prepare s (length + 1) nextIP).trans
    ((AgreesExcept.of_pushMem _ (pushAddr s) _).trans (AgreesExcept.of_enterFinish _ _ _))).trans
    (AgreesExcept.of_finishStep _)).mono (by simp)

/-- Preservation for an `ENTER size, 0`: if the 8 bytes at RSP - 8 lie below 4 GiB and outside
the page tables, the state after the step is ready to step again. -/
theorem ReadyToStep.afterStep_enter0 [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (size : BitVec 16) (nextIP : BitVec 64)
    (hlow : (pushAddr s).toNat + 8 ≤ 2^32)
    (htables : PageTableEntriesApart (pushAddr s).toNat 8) :
    ReadyToStep (afterStep s length fun t => enterState0 { t with Next_IP := nextIP } size) :=
  h.of_agreesExcept (AgreesExcept.afterStep_enter0 s length size nextIP) (by
    rw [afterStep_enter0_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables)

/-! ### After an `ENTER size, 1` step -/

/-- After an `ENTER size, 1` step, RIP is `nextIP`. -/
theorem afterStep_enter1_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (size : BitVec 16) (nextIP : BitVec 64) :
    (afterStep s length fun t => enterState1 { t with Next_IP := nextIP } size).RIP = nextIP := by
  simp [afterStep, finishStep, enterState1, enterFinish, checkAccess, pushMem, Operand.write,
    stackAccess, afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Memory after an `ENTER size, 1` step: RBP written at RSP - 8, then RSP - 8 at RSP - 16. -/
@[simp] theorem afterStep_enter1_external (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => enterState1 { t with Next_IP := nextIP } size).external =
      memStore (memStore s.external (pushAddr s) ((Operand.reg 5 : Operand 64).read s))
        (pushAddr s - 8) (pushAddr s) := rfl

/-- After an `ENTER size, 1` step, RSP is the old RSP - 16 - `size`. -/
theorem Operand.read_afterStep_enter1_rsp (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => enterState1 { t with Next_IP := nextIP } size) =
      pushAddr s - 8 - size.setWidth 64 := by
  rw [Operand.read_afterStep, enterState1, enterFinish, Operand.read_write_reg64_self]
  rfl

/-- After an `ENTER size, 1` step, RBP is the old RSP - 8. -/
theorem Operand.read_afterStep_enter1_rbp (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.reg 5 : Operand 64).read
      (afterStep s length fun t => enterState1 { t with Next_IP := nextIP } size) =
      pushAddr s := by
  rw [Operand.read_afterStep, enterState1, enterFinish, Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_write_reg64_self]
  rfl

/-- After an `ENTER size, 1` step, the 8 bytes at the old RSP - 8 hold the old RBP (the second
push, at RSP - 16, misses them). -/
theorem Operand.read_afterStep_enter1_mem (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.mem (pushAddr s) : Operand 64).read
      (afterStep s length fun t => enterState1 { t with Next_IP := nextIP } size) =
      (Operand.reg 5 : Operand 64).read s := by
  simp only [Operand.read, afterStep_enter1_external]
  refine (memLoad_congr fun j hj => ?_).trans (memLoad_memStore s.external (pushAddr s)
    (by decide) (by decide) _)
  simp only [memByte, PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  intro i hi he
  have hi' : i < 8 := hi
  have hj' : j < 8 := hj
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
    show (8 : BitVec 64).toNat = 8 from rfl] at this
  omega

/-- After an `ENTER size, 1` step, the 8 bytes at the old RSP - 16 hold the old RSP - 8. -/
theorem Operand.read_afterStep_enter1_mem2 (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.mem (pushAddr s - 8) : Operand 64).read
      (afterStep s length fun t => enterState1 { t with Next_IP := nextIP } size) =
      pushAddr s := by
  simp only [Operand.read, afterStep_enter1_external]
  exact memLoad_memStore _ _ (by decide) (by decide) _

/-- An `ENTER size, 1` step changes only RSP, RBP, the 16 bytes at RSP - 16 and RIP (besides the
bookkeeping). -/
theorem AgreesExcept.afterStep_enter1 (s : RamState) (length : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    AgreesExcept [.reg 4, .reg 5, .mem (pushAddr s) 8, .mem (pushAddr s - 8) 8, .rip] s
      (afterStep s length fun t => enterState1 { t with Next_IP := nextIP } size) :=
  (((AgreesExcept.prepare s (length + 1) nextIP).trans
    (((AgreesExcept.of_pushMem _ (pushAddr s) _).trans
      (AgreesExcept.of_pushMem _ (pushAddr s - 8) _)).trans
      (AgreesExcept.of_enterFinish _ _ _))).trans (AgreesExcept.of_finishStep _)).mono (by simp)

/-- Preservation for an `ENTER size, 1`: if the 8 bytes at RSP - 8 and those at RSP - 16 lie
below 4 GiB and outside the page tables, the state after the step is ready to step again. -/
theorem ReadyToStep.afterStep_enter1 [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (size : BitVec 16) (nextIP : BitVec 64)
    (hlow : (pushAddr s).toNat + 8 ≤ 2^32)
    (htables : PageTableEntriesApart (pushAddr s).toNat 8)
    (hlow2 : (pushAddr s - 8).toNat + 8 ≤ 2^32)
    (htables2 : PageTableEntriesApart (pushAddr s - 8).toNat 8) :
    ReadyToStep (afterStep s length fun t => enterState1 { t with Next_IP := nextIP } size) :=
  h.of_agreesExcept (AgreesExcept.afterStep_enter1 s length size nextIP) (by
    rw [afterStep_enter1_external]
    exact IdentityPageTableMemory.memStore
      (IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables) _ _ hlow2 htables2)

/-! ### Effects that avoid the code -/

/-- An effect that writes RSP and RBP, the 8 bytes at `a` apart from the code, and RIP (ENTER at
level 0) avoids the code. -/
theorem Effect.avoids_of_components_enter0 {e : Effect} {a : BitVec 64}
    (h : e.components = [.reg 4, .reg 5, .mem a 8, .rip]) {p : BitVec 64} {bytes : List UInt8}
    (hap : RangeApart a 8 p bytes.length) : e.Avoids (codeRange p bytes) := by
  intro x hx c hc hcov
  rw [h] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact hcov
  · exact hcov
  · obtain ⟨i, hi, hxe⟩ := hcov
    obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
    exact hap i hi j hj (hxe.symm.trans hxj)
  · exact hcov

/-- An effect that writes RSP and RBP, the 8 bytes at `a` and at `b` apart from the code, and RIP
(ENTER at level 1) avoids the code. -/
theorem Effect.avoids_of_components_enter1 {e : Effect} {a b : BitVec 64}
    (h : e.components = [.reg 4, .reg 5, .mem a 8, .mem b 8, .rip]) {p : BitVec 64}
    {bytes : List UInt8} (hap : RangeApart a 8 p bytes.length)
    (hbp : RangeApart b 8 p bytes.length) : e.Avoids (codeRange p bytes) := by
  intro x hx c hc hcov
  rw [h] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact hcov
  · exact hcov
  · obtain ⟨i, hi, hxe⟩ := hcov
    exact hap i hi j hj (hxe.symm.trans hxj)
  · obtain ⟨i, hi, hxe⟩ := hcov
    exact hbp i hi j hj (hxe.symm.trans hxj)
  · exact hcov

/-! ### Nesting levels 2–31 -/

theorem enter_forIn_run {ε : Type}
    (body : Int → BitVec 64 × BitVec 64 →
      X86.Runtime.SpecM ε RamState (ForInStep (BitVec 64 × BitVec 64)))
    (m : Nat) (a b : BitVec 64) (S : Nat → RamState)
    (h : ∀ i < m,
      (body (1 + i) (a - 8 * BitVec.ofNat 64 i, b - 8 * BitVec.ofNat 64 i)).run (S i) =
        (.ok (.yield (a - 8 * BitVec.ofNat 64 (i + 1), b - 8 * BitVec.ofNat 64 (i + 1))),
          S (i + 1))) :
    (forIn (X86.Runtime.intRange 1 m) (a, b) body).run (S 0) =
      (.ok (a - 8 * BitVec.ofNat 64 m, b - 8 * BitVec.ofNat 64 m), S m) := by
  have hr : X86.Runtime.intRange 1 m = (List.range' 0 m).map (fun i : Nat => (1 : Int) + i) := by
    simp only [X86.Runtime.intRange, show (m : Int) - 1 + 1 = m by omega, Int.toNat_natCast,
      List.range_eq_range']
  have := specM_forIn_range'_run (fun i : Nat => (1 : Int) + i) body
    (fun i => (a - 8 * BitVec.ofNat 64 i, b - 8 * BitVec.ofNat 64 i)) S m 0
    (fun i _ hi => h i (by omega))
  simpa [hr] using this

/-- One more slot down: `a - 8 i - 8 = a - 8 (i + 1)`. -/
theorem sub8_succ (a : BitVec 64) (i : Nat) :
    a - 8 * BitVec.ofNat 64 i - 8 = a - 8 * BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add, BitVec.mul_add, BitVec.sub_sub]
  rfl

/-- ENTER's loop from `t` (level `L ≥ 2`, `L - 1` passes), RSP `a` (after the push of RBP) and RBP
`b`: after `k` passes, for each `i < k` the 8 bytes at `b - 8 (i + 1)` were read (in the state
after the earlier passes) and pushed at `a - 8 (i + 1)`. -/
def enterCopies (t : RamState) (a b : BitVec 64) : Nat → RamState
  | 0 => t
  | k + 1 =>
    let u := enterCopies t a b k
    pushMem (dataAccess u "load") (a - 8 * BitVec.ofNat 64 (k + 1))
      ((Operand.mem (b - 8 * BitVec.ofNat 64 (k + 1)) : Operand 64).read u)

/-- The copies keep SS. -/
@[simp] theorem enterCopies_SS (u : RamState) (a b : BitVec 64) (k : Nat) :
    (enterCopies u a b k).SS = u.SS := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [enterCopies, pushMem_SS]
    exact ih

/-- Writable bytes stay writable through the copies. -/
theorem MemWritable.enterCopies {u : RamState} {x : BitVec 64} {len : Nat}
    (hw : MemWritable u x len) (a b : BitVec 64) (k : Nat) :
    MemWritable (X86Proofs.enterCopies u a b k) x len := by
  induction k with
  | zero => exact hw
  | succ k ih =>
    show MemWritable (X86Proofs.pushMem
      (X86Proofs.dataAccess (X86Proofs.enterCopies u a b k) "load") _ _) x len
    exact (ih.of_external_eq (t := dataAccess _ "load") rfl).pushMem _ _

/-- Readable bytes stay readable through the copies. -/
theorem MemReadable.enterCopies {u : RamState} {x : BitVec 64} {len : Nat}
    (hr : MemReadable u x len) (a b : BitVec 64) (k : Nat) :
    MemReadable (X86Proofs.enterCopies u a b k) x len := by
  induction k with
  | zero => exact hr
  | succ k ih =>
    show MemReadable (X86Proofs.pushMem
      (X86Proofs.dataAccess (X86Proofs.enterCopies u a b k) "load") _ _) x len
    exact ⟨ih.low, fun i hi => memStore_isSome _ _ _ _ (ih.mem i hi)⟩

/-- The data-access facts survive the copies if their slots are writable. -/
theorem DataReady.enterCopies [Bindings] {u : RamState} (h : DataReady u) (a b : BitVec 64)
    (k : Nat) (hw : ∀ j < k, MemWritable u (a - 8 * BitVec.ofNat 64 (j + 1)) 8) :
    DataReady (X86Proofs.enterCopies u a b k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    show DataReady (X86Proofs.pushMem
      (X86Proofs.dataAccess (X86Proofs.enterCopies u a b k) "load") _ _)
    exact (ih (fun j hj => hw j (by omega)) |>.dataAccess "load").pushMem
      ((MemWritable.enterCopies (hw k (by omega)) a b k).of_external_eq rfl) _

/-- The state after `ENTER size, L` (`2 ≤ L < 32`) from `t`: RBP pushed at RSP - 8, the `L - 1`
copies of the enclosing frames' pointers (`enterCopies`), the new frame pointer RSP - 8 pushed at
RSP - 8 - 8 L, RBP := RSP - 8, RSP := RSP - 8 - 8 L - `size`. -/
def enterStateN (t : RamState) (L : Nat) (size : BitVec 16) : RamState :=
  enterFinish (pushMem (enterCopies (pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t))
      (pushAddr t) ((Operand.reg 5 : Operand 64).read t) (L - 1))
      (pushAddr t - 8 * BitVec.ofNat 64 L) (pushAddr t))
    (pushAddr t) (pushAddr t - 8 * BitVec.ofNat 64 L - size.setWidth 64)

/-- `Operations.ENTER 64 64 size L` for `2 ≤ L < 32`: with the `L + 1` slots at RSP - 8 - 8 k
(`k ≤ L`) writable, the 8 bytes at RBP - 8 k (`0 < k < L`) readable and the final RSP below
4 GiB, the result is `enterStateN`. -/
theorem enter_operationN [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (size : BitVec 16) (L : Nat) (hL : 2 ≤ L) (hL' : L < 32)
    (hw : ∀ k ≤ L, MemWritable t (pushAddr t - 8 * BitVec.ofNat 64 k) 8)
    (hr : ∀ k < L - 1,
      MemReadable t ((Operand.reg 5 : Operand 64).read t - 8 * BitVec.ofNat 64 (k + 1)) 8)
    (hcheck : (pushAddr t - 8 * BitVec.ofNat 64 L - size.setWidth 64).toNat + 8 ≤ 2^32) :
    (X86.Instructions.Operations.ENTER 64 64 size (BitVec.ofNat 8 L)).run t =
      (.ok (), enterStateN t L size) := by
  have hw0 : MemWritable t (pushAddr t) 8 := by simpa using hw 0 (by omega)
  have hd := h.pushMem hw0 ((Operand.reg 5 : Operand 64).read t)
  unfold X86.Instructions.Operations.ENTER
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (get_run t)
  spec_bind_with (rsp_run t)
  spec_bind_with (get_run t)
  spec_bind_with (enterRbp_run t)
  spec_bind_with (pushStack_run t h hss (stackPtr t) _ (hw0 : MemWritable t (stackPtr t - 8) 8))
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (zeroExtend_full_run _ _)
  have hu : X86.Runtime.Unsigned (BitVec.ofNat 8 L) % 32 = (L : Int) := by
    rw [unsigned_eq]; simp; omega
  simp only [hu, show decide ((L : Int) > 0) = true by simp; omega, ↓reduceIte]
  spec_bind_with (rbp_run _)
  rw [show (L : Int) - 1 = ((L - 1 : Nat) : Int) by omega]
  have hrbp : (Operand.reg 5 : Operand 64).read ((Operand.mem (stackPtr t - 8) : Operand 64).write
      (stackAccess t) ((Operand.reg 5 : Operand 64).read t)) =
        (Operand.reg 5 : Operand 64).read t :=
    rfl
  simp only [hrbp]
  refine (specM_bind_run _ _ (enter_forIn_run _ (L - 1) _ _
    (enterCopies (pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t)) (pushAddr t)
      ((Operand.reg 5 : Operand 64).read t)) ?_)).trans ?_
  · intro i hi
    have hu := (hd.enterCopies (pushAddr t) ((Operand.reg 5 : Operand 64).read t) i
      (fun j hj => ((hw (j + 1) (by omega)).pushMem _ _)))
    have hssu : (enterCopies (pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t))
        (pushAddr t) ((Operand.reg 5 : Operand 64).read t) i).SS = userStackSegment := by
      rw [enterCopies_SS, pushMem_SS]; exact hss
    have hru := MemReadable.enterCopies
      (u := pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t))
      ⟨(hr i hi).low, fun j hj => memStore_isSome _ _ _ _ ((hr i hi).mem j hj)⟩
      (pushAddr t) ((Operand.reg 5 : Operand 64).read t) i
    have hwu := MemWritable.enterCopies ((hw (i + 1) (by omega)).pushMem (pushAddr t)
      ((Operand.reg 5 : Operand 64).read t)) (pushAddr t) ((Operand.reg 5 : Operand 64).read t) i
    spec_bind_with (checkedSliceRead_full_run _ _)
    spec_bind_rfl
    refine (specM_bind_run _ _
      (value := (Operand.reg 5 : Operand 64).read t - 8 * BitVec.ofNat 64 i - 8) rfl).trans ?_
    spec_bind_with (zeroExtend_full_run _ _)
    spec_bind_with (get_run _)
    spec_bind_with (checkedSliceRead_full_run _ _)
    spec_bind_with (zeroExtend_full_run _ _)
    rw [hssu, sub8_succ]
    spec_bind_with (logicalMemRead_run_seg _ hu _ _ _ (SegAccess.userStack _) 64 (by decide)
      .Memory_Read (.inl rfl) hru.low hru.mem)
    spec_bind_with (get_run _)
    spec_bind_with (get_run _)
    have hw' : MemWritable (dataAccess (enterCopies (pushMem t (pushAddr t)
        ((Operand.reg 5 : Operand 64).read t)) (pushAddr t) ((Operand.reg 5 : Operand 64).read t) i)
        "load") (stackPtr t - 8 - 8 * BitVec.ofNat 64 i - 8) 8 := by
      rw [sub8_succ]; exact hwu.of_external_eq rfl
    spec_bind_with (pushStack_run _ (hu.dataAccess "load") hssu
      (stackPtr t - 8 - 8 * BitVec.ofNat 64 i) _ hw')
    rw [sub8_succ]
    rfl
  · have hdL := hd.enterCopies (pushAddr t) ((Operand.reg 5 : Operand 64).read t) (L - 1)
      (fun j hj => ((hw (j + 1) (by omega)).pushMem _ _))
    have hssL : (enterCopies (pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t))
        (pushAddr t) ((Operand.reg 5 : Operand 64).read t) (L - 1)).SS = userStackSegment := by
      rw [enterCopies_SS, pushMem_SS]; exact hss
    have hwL : MemWritable
        (enterCopies (pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t))
        (pushAddr t) ((Operand.reg 5 : Operand 64).read t) (L - 1))
        (stackPtr t - 8 - 8 * BitVec.ofNat 64 (L - 1) - 8) 8 := by
      rw [sub8_succ, Nat.sub_add_cancel (by omega : 1 ≤ L)]
      exact MemWritable.enterCopies ((hw L (Nat.le_refl L)).pushMem _ _) _ _ _
    spec_bind_with (get_run _)
    spec_bind_with (get_run _)
    spec_bind_with (checkedSliceRead_full_run _ _)
    spec_bind_with (pushStack_run _ hdL hssL _ _ hwL)
    rw [sub8_succ, Nat.sub_add_cancel (by omega : 1 ≤ L)]
    have hwL' : MemWritable
        (enterCopies (pushMem t (pushAddr t) ((Operand.reg 5 : Operand 64).read t))
        (pushAddr t) ((Operand.reg 5 : Operand 64).read t) (L - 1))
        (pushAddr t - 8 * BitVec.ofNat 64 L) 8 :=
      MemWritable.enterCopies ((hw L (Nat.le_refl L)).pushMem _ _) _ _ _
    have hc := checkLogicalAddressIsWritable_run (pushMem (enterCopies (pushMem t (pushAddr t)
      ((Operand.reg 5 : Operand 64).read t)) (pushAddr t) ((Operand.reg 5 : Operand 64).read t)
        (L - 1)) (pushAddr t - 8 * BitVec.ofNat 64 L) (pushAddr t)) (hdL.pushMem hwL' _)
      (by rw [pushMem_SS]; exact hssL) (pushAddr t - 8 * BitVec.ofNat 64 L - size.setWidth 64) 64
      (by decide) hcheck
    spec_bind_with (zeroExtend16_run _ size)
    spec_bind_with (get_run _)
    spec_bind_with (checkedSliceRead_full_run _ _)
    spec_bind_with (zeroExtend_full_run _ _)
    spec_bind_with hc
    spec_bind_with (checkedSliceRead_full_run _ _)
    spec_bind_with (writeRBP64_run _ _)
    spec_bind_with (In64BitMode.writeRBP_oracle (in64BitMode_of_userCodeSegment
      (hdL.pushMem hwL' _).cs (hdL.pushMem hwL' _).efer.lma) _ _)
    exact writeRSP64_run _ _

/-- No wraparound below a frame: slot `k` (the 8 bytes at `a - 8 k`, `k < 32`) below 4 GiB is at
`a - 8 k` as a natural number. -/
theorem toNat_slot {a : BitVec 64} {k : Nat} (hk : k < 32)
    (h : (a - 8 * BitVec.ofNat 64 k).toNat + 8 ≤ 2^32) :
    (a - 8 * BitVec.ofNat 64 k).toNat = a.toNat - 8 * k ∧ 8 * k ≤ a.toNat := by
  have e : (8 * BitVec.ofNat 64 k).toNat = 8 * k := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]; simp; omega
  rw [BitVec.toNat_sub, e] at h ⊢
  have ha := a.isLt
  by_cases h8 : 8 * k ≤ a.toNat
  · refine ⟨?_, h8⟩
    rw [show 2 ^ 64 - 8 * k + a.toNat = 2 ^ 64 + (a.toNat - 8 * k) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- Two different slots below a frame, each below 4 GiB, are apart. -/
theorem slot_apart {a : BitVec 64} {j k : Nat} (hj : j < 32) (hk : k < 32) (hjk : j ≠ k)
    (hj' : (a - 8 * BitVec.ofNat 64 j).toNat + 8 ≤ 2^32)
    (hk' : (a - 8 * BitVec.ofNat 64 k).toNat + 8 ≤ 2^32) :
    RangeApart (a - 8 * BitVec.ofNat 64 j) 8 (a - 8 * BitVec.ofNat 64 k) 8 := by
  obtain ⟨ej, hj8⟩ := toNat_slot hj hj'
  obtain ⟨ek, hk8⟩ := toNat_slot hk hk'
  exact RangeApart.of_toNat (by omega) (by omega) (by rw [ej, ek]; omega)

/-- An 8-byte read at `x` after a push's write at `y` apart from it reads the bytes before. -/
theorem Operand.read_pushMem_of_apart (t : RamState) {x y : BitVec 64} (v : BitVec 64)
    (h : RangeApart x 8 y 8) :
    (Operand.mem x : Operand 64).read (pushMem t y v) = (Operand.mem x : Operand 64).read t := by
  simp only [Operand.read, pushMem, Operand.write]
  refine memLoad_congr fun j hj => ?_
  simp only [memByte, PhysicalMemory.read]
  rw [memStore_getElem?_of_ne]
  · rfl
  · intro i hi he
    exact h j hj i hi he.symm

/-- Bytes apart from the first `m` copies' slots read the same after them. -/
theorem Operand.read_enterCopies_of_apart (u : RamState) (a b x : BitVec 64) (m : Nat)
    (h : ∀ j < m, RangeApart x 8 (a - 8 * BitVec.ofNat 64 (j + 1)) 8) :
    (Operand.mem x : Operand 64).read (enterCopies u a b m) =
      (Operand.mem x : Operand 64).read u := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (Operand.mem x : Operand 64).read
      (pushMem (dataAccess (enterCopies u a b m) "load") _ _) = _
    rw [Operand.read_pushMem_of_apart _ _ (h m (by omega))]
    exact ih (fun j hj => h j (by omega))

/-- Copy `j` of the first `m` (`j < m`): slot `j + 1` holds the 8 bytes at `b - 8 (j + 1)` read
before it, if the later copies' slots are apart from it. -/
theorem Operand.read_enterCopies_slot (u : RamState) (a b : BitVec 64) (m j : Nat) (hj : j < m)
    (h : ∀ i < m, j < i → RangeApart (a - 8 * BitVec.ofNat 64 (j + 1)) 8
      (a - 8 * BitVec.ofNat 64 (i + 1)) 8) :
    (Operand.mem (a - 8 * BitVec.ofNat 64 (j + 1)) : Operand 64).read (enterCopies u a b m) =
      (Operand.mem (b - 8 * BitVec.ofNat 64 (j + 1)) : Operand 64).read (enterCopies u a b j) := by
  induction m with
  | zero => omega
  | succ m ih =>
    show (Operand.mem _ : Operand 64).read
      (pushMem (dataAccess (enterCopies u a b m) "load") _ _) = _
    by_cases hjm : j = m
    · subst hjm
      simp only [pushMem, Operand.read, Operand.write]
      exact memLoad_memStore _ _ (by decide) (by decide) _
    · rw [Operand.read_pushMem_of_apart _ _ (h m (by omega) (by omega))]
      exact ih (by omega) (fun i hi hji => h i (by omega) hji)

/-- What ENTER at nesting level `L` stores in slot `k ≤ L`, the 8 bytes at RSP - 8 - 8 k: the old
RBP (`k = 0`), the 8 bytes at RBP - 8 k (`0 < k < L`, the enclosing frames' pointers), the new
frame pointer RSP - 8 (`k = L`). -/
def enterSlotVal (s : RamState) (L k : Nat) : BitVec 64 :=
  if k = 0 then (Operand.reg 5 : Operand 64).read s
  else if k = L then pushAddr s
  else
    (Operand.mem ((Operand.reg 5 : Operand 64).read s - 8 * BitVec.ofNat 64 k) : Operand 64).read s

/-- The end of ENTER writes no memory. -/
theorem Operand.read_mem_enterFinish (u : RamState) (frame rsp x : BitVec 64) :
    (Operand.mem x : Operand 64).read (enterFinish u frame rsp) =
      (Operand.mem x : Operand 64).read u := rfl

/-- After `enterStateN`, slot `k ≤ L` holds `enterSlotVal`, if the slots are below 4 GiB and the
bytes read at RBP - 8 j are apart from them. -/
theorem Operand.read_enterStateN_slot (t : RamState) (L : Nat) (size : BitVec 16) (hL : 2 ≤ L)
    (hL' : L < 32) (k : Nat) (hk : k ≤ L)
    (hlow : ∀ k ≤ L, (pushAddr t - 8 * BitVec.ofNat 64 k).toNat + 8 ≤ 2^32)
    (hap : ∀ j, 0 < j → j < L → ∀ k ≤ L, RangeApart
      ((Operand.reg 5 : Operand 64).read t - 8 * BitVec.ofNat 64 j) 8
      (pushAddr t - 8 * BitVec.ofNat 64 k) 8) :
    (Operand.mem (pushAddr t - 8 * BitVec.ofNat 64 k) : Operand 64).read (enterStateN t L size) =
      enterSlotVal t L k := by
  have sa (i j : Nat) (hi : i ≤ L) (hj : j ≤ L) (hij : i ≠ j) :=
    slot_apart (a := pushAddr t) (by omega) (by omega) hij (hlow i hi) (hlow j hj)
  have h0 : pushAddr t - 8 * BitVec.ofNat 64 0 = pushAddr t := by simp
  rw [enterStateN, Operand.read_mem_enterFinish]
  by_cases hkL : k = L
  · subst hkL
    simp only [pushMem, Operand.read, Operand.write, enterSlotVal, show k ≠ 0 by omega,
      ↓reduceIte]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  rw [Operand.read_pushMem_of_apart _ _ (sa k L hk (Nat.le_refl L) hkL)]
  by_cases hk0 : k = 0
  · subst hk0
    rw [Operand.read_enterCopies_of_apart _ _ _ _ _ (fun j hj => sa 0 (j + 1) (by omega) (by omega)
      (by omega)), h0]
    simp only [pushMem, Operand.read, Operand.write, enterSlotVal, ↓reduceIte]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Operand.read_enterCopies_slot _ _ _ _ _ (by omega)
      (fun i hi hji => sa (j + 1) (i + 1) (by omega) (by omega) (by omega)),
    Operand.read_enterCopies_of_apart _ _ _ _ _
      (fun i hi => hap (j + 1) (by omega) (by omega) (i + 1) (by omega)),
    Operand.read_pushMem_of_apart _ _ (by
      have := hap (j + 1) (by omega) (by omega) 0 (by omega)
      rwa [h0] at this)]
  simp only [enterSlotVal, show j + 1 ≠ 0 by omega, hkL, ↓reduceIte]

/-- The first `m` copies change only their slots (besides the bookkeeping). -/
theorem AgreesExcept.of_enterCopies (u : RamState) (a b : BitVec 64) (m : Nat) :
    AgreesExcept ((List.range m).map fun j => Component.mem (a - 8 * BitVec.ofNat 64 (j + 1)) 8) u
      (enterCopies u a b m) := by
  induction m with
  | zero => exact AgreesExcept.refl _ u
  | succ m ih =>
    refine ((ih.trans (AgreesExcept.of_dataAccess _ "load")).trans
      (AgreesExcept.of_pushMem _ _ _)).mono ?_
    intro c hc
    simp only [List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil, List.mem_cons,
      or_false] at hc ⊢
    rcases hc with ⟨j, hj, rfl⟩ | rfl
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨m, by omega, rfl⟩

/-- The page tables survive the first `m` copies if their slots are below 4 GiB and outside the
tables. -/
theorem IdentityPageTableMemory.enterCopies {u : RamState}
    (h : IdentityPageTableMemory u.external) (a b : BitVec 64) (m : Nat)
    (hw : ∀ j < m, MemWritable u (a - 8 * BitVec.ofNat 64 (j + 1)) 8) :
    IdentityPageTableMemory (X86Proofs.enterCopies u a b m).external := by
  induction m with
  | zero => exact h
  | succ m ih =>
    exact IdentityPageTableMemory.memStore (ih fun j hj => hw j (by omega)) _ _
      (hw m (by omega)).low (hw m (by omega)).tables

/-- The copies change only memory, the oracle and the trace. -/
theorem enterCopies_eq (u : RamState) (a b : BitVec 64) (m : Nat) :
    ∃ e o tr,
      enterCopies u a b m = { u with external := e, oracle := o, traceEventsRev := tr } := by
  induction m with
  | zero => exact ⟨u.external, u.oracle, u.traceEventsRev, rfl⟩
  | succ m ih =>
    obtain ⟨e, o, tr, he⟩ := ih
    refine ⟨memStore e (a - 8 * BitVec.ofNat 64 (m + 1))
      ((Operand.mem (b - 8 * BitVec.ofNat 64 (m + 1)) : Operand 64).read (enterCopies u a b m)),
      oracleSkip (oracleSkip o 464) 336, ("isa.memory", "store") :: ("isa.memory", "load") :: tr,
      ?_⟩
    show pushMem (dataAccess (enterCopies u a b m) "load") _ _ = _
    rw [he]
    rfl

/-- `ENTER size, L` keeps CS. -/
@[simp] theorem enterStateN_CS (t : RamState) (L : Nat) (size : BitVec 16) :
    (enterStateN t L size).CS = t.CS := by
  obtain ⟨e, o, tr, he⟩ := enterCopies_eq (pushMem t (pushAddr t)
    ((Operand.reg 5 : Operand 64).read t)) (pushAddr t) ((Operand.reg 5 : Operand 64).read t)
    (L - 1)
  simp only [enterStateN, he]
  simp [enterFinish, checkAccess, pushMem, Operand.write, stackAccess]

/-- `ENTER size, L` keeps IA32_EFER. -/
@[simp] theorem enterStateN_IA32_EFER (t : RamState) (L : Nat) (size : BitVec 16) :
    (enterStateN t L size).IA32_EFER = t.IA32_EFER := by
  obtain ⟨e, o, tr, he⟩ := enterCopies_eq (pushMem t (pushAddr t)
    ((Operand.reg 5 : Operand 64).read t)) (pushAddr t) ((Operand.reg 5 : Operand 64).read t)
    (L - 1)
  simp only [enterStateN, he]
  simp [enterFinish, checkAccess, pushMem, Operand.write, stackAccess]

/-- After an `ENTER size, L` step (`2 ≤ L < 32`), RIP is `nextIP`. -/
theorem afterStep_enterN_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (L : Nat) (size : BitVec 16) (nextIP : BitVec 64) :
    (afterStep s length fun t => enterStateN { t with Next_IP := nextIP } L size).RIP =
      nextIP := by
  let t := { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP }
  obtain ⟨e, o, tr, he⟩ := enterCopies_eq (pushMem t (pushAddr t)
    ((Operand.reg 5 : Operand 64).read t)) (pushAddr t) ((Operand.reg 5 : Operand 64).read t)
    (L - 1)
  simp only [afterStep, enterStateN]
  rw [he]
  simp [finishStep, enterFinish, checkAccess, pushMem, Operand.write, stackAccess, t,
    afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After an `ENTER size, L` step, RSP is the old RSP - 8 - 8 L - `size`. -/
theorem Operand.read_afterStep_enterN_rsp (s : RamState) (length L : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => enterStateN { t with Next_IP := nextIP } L size) =
      pushAddr s - 8 * BitVec.ofNat 64 L - size.setWidth 64 := by
  rw [Operand.read_afterStep, enterStateN, enterFinish, Operand.read_write_reg64_self]
  rfl

/-- After an `ENTER size, L` step, RBP is the old RSP - 8. -/
theorem Operand.read_afterStep_enterN_rbp (s : RamState) (length L : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.reg 5 : Operand 64).read
      (afterStep s length fun t => enterStateN { t with Next_IP := nextIP } L size) =
      pushAddr s := by
  rw [Operand.read_afterStep, enterStateN, enterFinish, Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_write_reg64_self]
  rfl

/-- After an `ENTER size, L` step, slot `k ≤ L` (the 8 bytes at RSP - 8 - 8 k) holds
`enterSlotVal s L k`. -/
theorem Operand.read_afterStep_enterN_slot (s : RamState) (length L : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) (hL : 2 ≤ L) (hL' : L < 32) (k : Nat) (hk : k ≤ L)
    (hlow : ∀ k ≤ L, (pushAddr s - 8 * BitVec.ofNat 64 k).toNat + 8 ≤ 2^32)
    (hap : ∀ j, 0 < j → j < L → ∀ k ≤ L, RangeApart
      ((Operand.reg 5 : Operand 64).read s - 8 * BitVec.ofNat 64 j) 8
      (pushAddr s - 8 * BitVec.ofNat 64 k) 8) :
    (Operand.mem (pushAddr s - 8 * BitVec.ofNat 64 k) : Operand 64).read
      (afterStep s length fun t => enterStateN { t with Next_IP := nextIP } L size) =
      enterSlotVal s L k := by
  rw [Operand.read_afterStep]
  exact Operand.read_enterStateN_slot _ L size hL hL' k hk hlow hap

/-- An `ENTER size, L` step changes only RSP, RBP, the `L + 1` slots below RSP and RIP (besides
the bookkeeping). -/
theorem AgreesExcept.afterStep_enterN (s : RamState) (length L : Nat) (size : BitVec 16)
    (nextIP : BitVec 64) (hL : 1 ≤ L) :
    AgreesExcept ([.reg 4, .reg 5] ++ (List.range (L + 1)).map
        (fun k => Component.mem (pushAddr s - 8 * BitVec.ofNat 64 k) 8) ++ [.rip]) s
      (afterStep s length fun t => enterStateN { t with Next_IP := nextIP } L size) := by
  refine (((AgreesExcept.prepare s (length + 1) nextIP).trans
    ((((AgreesExcept.of_pushMem _ (pushAddr s) _).trans
      (AgreesExcept.of_enterCopies _ _ _ (L - 1))).trans
      (AgreesExcept.of_pushMem _ _ _)).trans (AgreesExcept.of_enterFinish _ _ _))).trans
    (AgreesExcept.of_finishStep _)).mono ?_
  intro c hc
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false, List.nil_append] at hc ⊢
  rcases hc with ((((rfl | ⟨j, hj, rfl⟩) | rfl) | (rfl | rfl)) | rfl)
  · exact Or.inl (Or.inr ⟨0, by omega, by simp⟩)
  · exact Or.inl (Or.inr ⟨j + 1, by omega, rfl⟩)
  · exact Or.inl (Or.inr ⟨L, by omega, rfl⟩)
  · simp
  · simp
  · simp

/-- Preservation for an `ENTER size, L`: if the `L + 1` slots below RSP lie below 4 GiB and outside
the page tables (writable), the state after the step is ready to step again. -/
theorem ReadyToStep.afterStep_enterN [Bindings] {s : RamState} (h : ReadyToStep s)
    (length L : Nat) (size : BitVec 16) (nextIP : BitVec 64) (hL : 1 ≤ L)
    (hw : ∀ k ≤ L, MemWritable s (pushAddr s - 8 * BitVec.ofNat 64 k) 8) :
    ReadyToStep (afterStep s length fun t => enterStateN { t with Next_IP := nextIP } L size) := by
  have hw0 : MemWritable s (pushAddr s) 8 := by simpa using hw 0 (by omega)
  refine h.of_agreesExcept (AgreesExcept.afterStep_enterN s length L size nextIP hL) ?_
  let T : RamState := { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP }
  have h0 : IdentityPageTableMemory
      (pushMem T (pushAddr T) ((Operand.reg 5 : Operand 64).read T)).external :=
    IdentityPageTableMemory.memStore (n := 64) h.memory.tables _ _ hw0.low hw0.tables
  have h1 := IdentityPageTableMemory.enterCopies h0 (pushAddr T)
    ((Operand.reg 5 : Operand 64).read T)
    (L - 1) (fun j hj => ((hw (j + 1) (by omega)).of_external_eq (t := T) rfl).pushMem _ _)
  exact IdentityPageTableMemory.memStore (n := 64) h1 _ (pushAddr T) (hw L (Nat.le_refl L)).low
    (hw L (Nat.le_refl L)).tables

/-- An effect that writes RSP and RBP, the `L + 1` slots below `a` apart from the code, and RIP
(ENTER at level `L ≥ 2`) avoids the code. -/
theorem Effect.avoids_of_components_enterN {e : Effect} {a : BitVec 64} {L : Nat}
    (h : e.components = [.reg 4, .reg 5] ++ (List.range (L + 1)).map
      (fun k => Component.mem (a - 8 * BitVec.ofNat 64 k) 8) ++ [.rip]) {p : BitVec 64}
    {bytes : List UInt8}
    (hap : ∀ k ≤ L, RangeApart (a - 8 * BitVec.ofNat 64 k) 8 p bytes.length) :
    e.Avoids (codeRange p bytes) := by
  intro x hx c hc hcov
  rw [h] at hc
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
  rcases hc with ((rfl | rfl) | ⟨k, hk, rfl⟩) | rfl
  · exact hcov
  · exact hcov
  · obtain ⟨i, hi, hxe⟩ := hcov
    exact hap k (by omega) i hi j hj (hxe.symm.trans hxj)
  · exact hcov

end X86Proofs
