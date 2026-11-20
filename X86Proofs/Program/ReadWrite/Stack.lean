import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Step.Address
import X86Proofs.Program.ComposeAttr

/-!
# The stack: pushes and pops of 8 bytes at RSP

Shared by PUSH and POP, and meant for CALL (push the return address, then branch) and RET (pop
RIP). lean-x86 does a 64-bit push with `Push_Stack` and a 64-bit pop with `Pop_Stack`:

- `pushStack_run`: `Push_Stack SS rsp CS 64 64 v` writes `v` at `rsp - 8` and returns
  `rsp - 8`. It does not go through `Logical_Mem_Write`: it builds the linear address itself
  (`Create_Linear_Address`, 336 oracle bits rather than `Create_Logical_Address`'s 464) and checks
  canonicality of `rsp - 8`, alignment (only with CR0.AM set at CPL 3), write permission on SS (a
  no-op in 64-bit mode) and data breakpoints. The bookkeeping is `stackAccess` (336 oracle bits
  and a `store` trace event). No shadow-stack (CET) access: the shadow stack is CALL's and RET's
  business, and it is off (`Prelude.CR4.ControlFlowEnforcementDisabled`, part of `ReadyToStep`).
- `popStack_run`: `Pop_Stack SS rsp 64 64` reads the 8 bytes at `rsp` through
  `Logical_Mem_Read` on the flat stack segment (`logicalMemRead_run`, bookkeeping
  `dataAccess s "load"`) and returns them with `rsp + 8`.
- `push_operation`: lean-x86's `Operations.PUSH 64` (the push plus the RSP write), with result
  `pushState`; `pop_operation`: `Operations.POP 64` returns the value and RSP + 8, which the form
  writes to RSP (`writeRSP64_run`) before the destination, giving `popState`.

Preconditions (the same shapes as the store and load layers):
- `PushPre p len`: a push from an instruction of `len` bytes at `p` is `StorePre` at `pushAddr`
  (RSP - 8) for 8 bytes: below 4 GiB, present in RAM, outside the page tables, and apart from the
  instruction's own bytes (it may cross a 4 KiB page, as `Logical_Mem_Write` may). RSP - 8 must not
  wrap below 0 (`MemWritable.low` rules it out).
- `PopPre p`: `LoadPre` at RSP for 8 bytes (below 4 GiB, present; may cross a page).

What a step does around the form (`afterStep`), as for stores and loads:
- push: `afterStep_push_rip`, `Operand.read_afterStep_push_rsp` (RSP = old RSP - 8),
  `Operand.read_afterStep_push_mem` (the 8 bytes at old RSP - 8 hold the value),
  `ReadyToStep.afterStep_push`, `AgreesExcept.afterStep_push` (frame `[.reg 4, .mem (RSP - 8) 8,
  .rip]`).
- pop into register `r`: `afterStep_pop_rip`, `Operand.read_afterStep_pop` (`r` = the 8 bytes at
  old RSP), `Operand.read_afterStep_pop_rsp` (RSP = old RSP + 8, if `r` is not RSP),
  `ReadyToStep.afterStep_pop`, `AgreesExcept.afterStep_pop` (frame `[.reg r, .reg 4, .rip]`). `pop
  rsp` sets RSP to the value read: lean-x86 writes RSP + 8 first, then the destination.
- `pushEffect`, `StepEffect.of_push`: the step of a push form with its effect, from its step
  theorem; `pushEffect_avoids` and `Triple.of_push`: its triple.

`isShadowStackEnabled_run`: CALL's and RET's shadow-stack test is false (CR4.CET clear).

PUSH FS and PUSH GS push with `Push_Stack`'s `check_lass` set: `pushStack_run` with `checkLASS`,
the same result.

16-bit pushes and pops (`66 50+r`, `66 58+r`): `pushStack16_run`, `popStack16_run`,
`push16_operation`, `pop16_operation`, the states `pushState16` (2 bytes at `pushAddr16` = RSP - 2)
and `popState16` (the register's low 16 bits), their step lemmas, `Push16Pre`, `Pop16Pre`,
`push16Effect` and `StepEffect.of_push16`. 16-bit `LEAVE` (`66 C9`, `leave16_operation`):
`Pop_Stack` of 2 bytes at RBP, RSP := RBP + 2, the low 16 bits of RBP := the value read
(`leaveState16`, `writeRBP16_run`), with the step lemmas `afterStep_leave16_rip` & co.

`LEAVE` (`leave_operation`, `Operations.LEAVE 64`): `Pop_Stack` at RBP, RSP := RBP + 8, RBP := the
value read (`leaveState`; `rbp_run`, `writeRSP64_run`, `writeRBP64_run`), and what a step whose form
ends in it does: `afterStep_leave_rip`, `Operand.read_afterStep_leave_rsp`,
`Operand.read_afterStep_leave_rbp`, `AgreesExcept.afterStep_leave` (`[.reg 4, .reg 5, .rip]`),
`ReadyToStep.afterStep_leave`.

Shared pieces CALL and RET can reuse without the PUSH/POP form shape: `ReadyToStep.of_agreesExcept`
(a state that agrees with a ready state outside some components and keeps the page tables is
ready), `AgreesExcept.prepare`, `AgreesExcept.of_pushState`, `AgreesExcept.of_popState`,
`AgreesExcept.of_finishStep` (compose with `AgreesExcept.trans`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-! ### `Create_Linear_Address` -/

/-- The linear-address record `Create_Linear_Address` builds for an 8-byte access at `address`
(64-bit mode), and the oracle after the 336 bits it draws (offset, and a physical address and
translation record for each of the two pages). -/
noncomputable def linearAddressFromOracle (o : X86.Runtime.Oracle) (ds : Segment) (cpl : Int)
    (address : BitVec 64) : Address_Translation × X86.Runtime.Oracle :=
  let (offset, o) := o.take 64
  let (pa1, o) := o.take 64
  let (tr1, o) := translationFromOracle o address pa1 .Memory_Type_Unknown
  let (pa2, o) := o.take 64
  let (tr2, o) := translationFromOracle o address pa2 .Memory_Type_Unknown
  ({ num_bytes := 8, segment := nullDataSegment ds, offset := offset,
     linear_address := address, is_implicit_supervisor_mode_access := false,
     is_shadow_stack_access := false, translation_cpl := cpl,
     is_split_access := false, translation1 := tr1, translation2 := tr2 }, o)

theorem linearAddressFromOracle_oracle (o : X86.Runtime.Oracle) (ds : Segment) (cpl : Int)
    (address : BitVec 64) :
    (linearAddressFromOracle o ds cpl address).2 = oracleSkip o 336 := by
  simp [linearAddressFromOracle, translationFromOracle, oracleTake_snd, oracleSkip_oracleSkip]

theorem createTranslation_run (t : RamState) (la pa : BitVec 64) :
    (Create_Translation la pa .Memory_Type_Unknown).run t =
      (.ok (translationFromOracle t.oracle la pa .Memory_Type_Unknown).1,
        { t with oracle := (translationFromOracle t.oracle la pa .Memory_Type_Unknown).2 }) := rfl

/-- `Create_Linear_Address` for 8 bytes in 64-bit mode (EFER.LMA = 1): the linear address is the
address itself; 336 oracle bits are drawn. -/
theorem createLinearAddress64_run (s : RamState) (address : BitVec 64)
    (hlma : s.IA32_EFER.LMA = 1) :
    (Create_Linear_Address address 64).run s =
      (.ok (linearAddressFromOracle s.oracle s.DS s.CPL address).1,
        { s with oracle := oracleSkip s.oracle 336 }) := by
  rw [← linearAddressFromOracle_oracle s.oracle s.DS s.CPL address]
  unfold Create_Linear_Address
  spec_run [MonadState.get => get_run _]
  dsimp only
  rw [hlma]
  spec_run [MonadState.get => get_run _, Create_Translation => createTranslation_run _ _ _]

/-- With `CR4.CET` clear, the CET shadow stack is off (for CALL and RET, which ask; PUSH and POP
do not). The end-branch counterpart is `isEndBranchEnabledAndNotSuppressed_run` (`Instructions/Branch/Form.lean`). -/
theorem isShadowStackEnabled_run {σ : Type} (s : X86.State σ) (hcpl : 0 ≤ s.CPL ∧ s.CPL ≤ 3)
    (hcr4 : Prelude.SupportedIntegerCR4 s.CR4) :
    (CET.Is_Shadow_Stack_Enabled s.CPL).run s = (.ok false, s) := by
  simp [CET.Is_Shadow_Stack_Enabled, cr4CET_eq, cr0PE_eq, rflagsVM_eq, x86_runtime, hcpl,
    HAnd.hAnd, AndOp.and, strictAnd, supportedIntegerCR4_extractLsb_cet hcr4, bind, pure, get,
    getThe, ExceptT.bind, ExceptT.pure, ExceptT.run, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    StateT.pure, MonadStateOf.get, StateT.get, Functor.map, StateT.map, Bind.bind, Pure.pure,
    ExceptT.lift, liftM, monadLift, MonadLift.monadLift]

/-! ### `Push_Stack` and `Pop_Stack` -/

/-- A 64-bit register reads what was written to it. -/
theorem Operand.read_write_reg64_self (t : RamState) (r : BitVec 5) (v : BitVec 64) :
    (Operand.reg r : Operand 64).read ((Operand.reg r : Operand 64).write t v) = v := by
  simp

/-- RSP (register 4). -/
def stackPtr (s : RamState) : BitVec 64 := s.GPR[gprIndex 4]

/-- The address a 64-bit push writes: RSP - 8. -/
def pushAddr (s : RamState) : BitVec 64 := stackPtr s - 8

/-- The bookkeeping of a push (`Push_Stack`): 336 oracle bits for `Create_Linear_Address`, and a
`store` event in lean-x86's trace of memory accesses. -/
def stackAccess (s : RamState) : RamState :=
  { s with oracle := oracleSkip s.oracle 336,
           traceEventsRev := ("isa.memory", "store") :: s.traceEventsRev }

/--
`Push_Stack` of a 64-bit value at RSP = `rsp` through the flat stack segment, with the 8 bytes at
`rsp - 8` writable in place: writes `v` there and returns `rsp - 8`. The checks it makes pass:
`rsp - 8` is canonical (below 4 GiB), alignment checking is off (CR0.AM clear), SS is writable in
64-bit mode, and data breakpoints are disabled. With `checkLASS` (lean-x86's `check_lass`, which
PUSH FS and PUSH GS set) it also checks LASS, which is off; the result is the same.
-/
theorem pushStack_run [Bindings] (s : RamState) (h : DataReady s) (hss : s.SS = userStackSegment)
    (rsp v : BitVec 64) (hw : MemWritable s (rsp - 8) 8) (checkLASS : Bool := false) :
    (Push_Stack s.SS rsp s.CS 64 64 v checkLASS).run s =
      (.ok (rsp - 8 : BitVec 64),
        (Operand.mem (rsp - 8) : Operand 64).write (stackAccess s) v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 336 }
  have ht : DataReady t := h.oracle _
  have hcan := isCanonicalWrtPagingMode_run s (rsp - 8) 8 h.cr0 h.cr4 h.efer.lme h.lam (by have := hw.low; omega) hw.low
  have hcpl : 0 ≤ X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ∧
      X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ≤ 3 := by decide
  cases checkLASS
  · let linear : Address_Translation :=
      { (linearAddressFromOracle s.oracle s.DS s.CPL (rsp - 8)).1 with
        translation_cpl := X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) }
    have htr := translateLinearToPhysical_run_of_dataReady t ht linear .Memory_Write 8 rfl (by decide) rfl hw.low
    have hphys := physicalMemWrite_dataPhysical_run linear (rsp - 8) rfl 64 (by decide) rfl v t
      ht.smrr hcpl hw.mem
    unfold Push_Stack
    rw [hss, h.cs]
    spec_run [MonadState.get => get_run _, Is_64Bit_Code_Segment => is64BitCodeSegment_userCodeSegment_run _ h.efer.lma,
      Is_Canonical_Wrt_Paging_Mode => hcan,
      Create_Linear_Address => createLinearAddress64_run _ _ h.efer.lma,
      Is_Alignment_Checking_Enabled => isAlignmentCheckingEnabled_run _ ht.cr0,
      Check_Write_Permission => checkWritePermission_run _ _ ht.cs ht.efer.lma,
      Check_Data_Write_Breakpoint => checkDataWriteBreakpoint_run _ _ _ ht.debug,
      Translate_Linear_To_Physical.interpreted => htr,
      Physical_Mem_Write => hphys]
  · let linear : Address_Translation :=
      { (linearAddressFromOracle s.oracle s.DS s.CPL (rsp - 8)).1 with
        segment := userStackSegment
        translation_cpl := X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) }
    have htr := translateLinearToPhysical_run_of_dataReady t ht linear .Memory_Write 8 rfl (by decide) rfl hw.low
    have hphys := physicalMemWrite_dataPhysical_run linear (rsp - 8) rfl 64 (by decide) rfl v t
      ht.smrr hcpl hw.mem
    unfold Push_Stack
    rw [hss, h.cs]
    spec_run [MonadState.get => get_run _, Is_64Bit_Code_Segment => is64BitCodeSegment_userCodeSegment_run _ h.efer.lma,
      Is_Canonical_Wrt_Paging_Mode => hcan,
      Create_Linear_Address => createLinearAddress64_run _ _ h.efer.lma,
      Is_Alignment_Checking_Enabled => isAlignmentCheckingEnabled_run _ ht.cr0,
      Check_LASS_Violation => checkLASSViolation_run _ _ ht.lass,
      Check_Write_Permission => checkWritePermission_run _ _ ht.cs ht.efer.lma,
      Check_Data_Write_Breakpoint => checkDataWriteBreakpoint_run _ _ _ ht.debug,
      Translate_Linear_To_Physical.interpreted => htr,
      Physical_Mem_Write => hphys]

theorem stackAddressSize_run (s : RamState) (hmode : In64BitMode s) :
    (Stack_Address_Size userStackSegment).run s = (.ok 64, s) := by
  unfold Stack_Address_Size
  spec_run [MonadState.get => get_run _, In_64Bit_Mode => hmode]

theorem checkedSliceRead_full_run (s : RamState) (x : BitVec 64) :
    (X86.Runtime.CheckedSlice.read x 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run s = (.ok x, s) := by
  simp [X86.Runtime.CheckedSlice.read, x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk,
    StateT.pure]

theorem zeroExtend_full_run (s : RamState) (x : BitVec 64) :
    (Std.Bits.Zero_Extend (source_size := 64) x 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run s = (.ok x, s) := by
  simp [x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.pure]

/--
`Pop_Stack` of 64 bits at RSP = `rsp` through the flat stack segment, with the 8 bytes at `rsp`
readable: returns them and `rsp + 8`; the bookkeeping is a data load's (`dataAccess s "load"`).
(`spec_run` times out here, so the binds are stepped by hand.)
-/
theorem popStack_run [Bindings] (s : RamState) (h : DataReady s) (hss : s.SS = userStackSegment)
    (rsp : BitVec 64) (hr : MemReadable s rsp 8) :
    (Pop_Stack s.SS rsp 64 64).run s =
      (.ok ((Operand.mem rsp : Operand 64).read s, (rsp + 8 : BitVec 64)),
        dataAccess s "load") := by
  have hread := logicalMemRead_run s h true rsp 64 (by decide) .Memory_Read (.inl rfl)
    hr.low hr.mem
  have hmode := in64BitMode_of_userCodeSegment h.cs h.efer.lma
  unfold Pop_Stack
  rw [hss]
  simp only [show (0 : Int) ≤ 64 from by decide, decide_true, beq_self_eq_true, Bool.or_true,
    assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (s := s) (t := s) (value := true) rfl).trans ?_
  refine (specM_bind_run _ _ (s := s) (t := s) (value := ()) rfl).trans ?_
  refine (specM_bind_run _ _ (stackAddressSize_run s hmode)).trans ?_
  refine (specM_bind_run (Std.Integer.Positive_Divide 64 8 :
    X86.Runtime.SpecM X86.Exception RamState Int) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run (liftM (Null_Segment userStackSegment)) _ (s := s) (t := s)
    (value := flatData true) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.CheckedSlice.read rsp 0 64) _ (s := s) (t := s)
    (value := rsp) (checkedSliceRead_full_run s rsp)).trans ?_
  refine (specM_bind_run (Std.Bits.Zero_Extend (source_size := 64) rsp 64) _ (s := s) (t := s)
    (value := rsp) (zeroExtend_full_run s rsp)).trans ?_
  refine (specM_bind_run _ _ hread).trans ?_
  refine (specM_bind_run _ _ (s := dataAccess s "load") (t := dataAccess s "load")
    (value := (rsp + 8 : BitVec 64)) rfl).trans ?_
  simp only [show ((64 : Int) == 16) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (checkedSliceRead_full_run _ _)).trans ?_
  exact (specM_bind_run _ _ (zeroExtend_full_run _ _)).trans rfl

/-! ### `Operations.PUSH` and `Operations.POP` at 64 bits -/

/-- The state after a 64-bit push of `v` from `t`: the 8 bytes at RSP - 8 hold `v`, RSP is
RSP - 8, plus the bookkeeping (`stackAccess`). -/
def pushState (t : RamState) (v : BitVec 64) : RamState :=
  (Operand.reg 4 : Operand 64).write
    ((Operand.mem (pushAddr t) : Operand 64).write (stackAccess t) v) (pushAddr t)

/-- The state after a 64-bit pop into register `r` from `t`: RSP is RSP + 8, then `r` is the 8
bytes at the old RSP (so `pop rsp` leaves RSP = the value read), plus the bookkeeping
(`dataAccess t "load"`). -/
def popState (t : RamState) (r : BitVec 5) : RamState :=
  (Operand.reg r : Operand 64).write
    ((Operand.reg 4 : Operand 64).write (dataAccess t "load") (stackPtr t + 8))
    ((Operand.mem (stackPtr t) : Operand 64).read t)

theorem rsp_run (s : RamState) :
    (RSP : X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run s = (.ok (stackPtr s), s) :=
  rfl

theorem rspWrite_run (s : RamState) (v : BitVec 64) :
    (RSP_write v : X86.Runtime.SpecM X86.Exception RamState Unit).run s =
      (.ok (), (Operand.reg 4 : Operand 64).write s v) := by
  rw [Operand.write_reg64]
  rfl

/-- `Operations.PUSH 64 v`: with RSP - 8 writable, the push is `pushState`. -/
theorem push_operation [Bindings] (t : RamState) (h : DataReady t) (hss : t.SS = userStackSegment)
    (v : BitVec 64) (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.Operations.PUSH 64 v).run t = (.ok (), pushState t v) := by
  unfold X86.Instructions.Operations.PUSH
  spec_run [MonadState.get => get_run _, RSP => rsp_run _,
    Push_Stack => pushStack_run t h hss (stackPtr t) v hw, RSP_write => rspWrite_run _ _]

/-- `Operations.POP 64`: with the 8 bytes at RSP readable, the pop returns them and the new stack
pointer RSP + 8, which it leaves to the form to write. -/
theorem pop_operation [Bindings] (t : RamState) (h : DataReady t) (hss : t.SS = userStackSegment)
    (hr : MemReadable t (stackPtr t) 8) :
    (X86.Instructions.Operations.POP 64).run t =
      (.ok ((Operand.mem (stackPtr t) : Operand 64).read t, (stackPtr t + 8 : BitVec 64)),
        dataAccess t "load") := by
  unfold X86.Instructions.Operations.POP
  spec_run [MonadState.get => get_run _, RSP => rsp_run _,
    Pop_Stack => popStack_run t h hss (stackPtr t) hr]

/-! ### Preconditions -/

/-- The precondition of a push triple at `p`, for an instruction of `codeLen` bytes: RIP = `p`,
and the 8 bytes at RSP - 8 can be written in place and miss the instruction's bytes. -/
abbrev PushPre (p : BitVec 64) (codeLen : Nat) : RamState → Prop :=
  StorePre p codeLen pushAddr 8

/-- The precondition of a pop triple at `p`: RIP = `p`, and the 8 bytes at RSP can be read. -/
abbrev PopPre (p : BitVec 64) : RamState → Prop :=
  LoadPre p stackPtr 8

/-! ### Readiness and frames, piece by piece -/

/-- Clearing the status flags keeps every other bit of RFLAGS. -/
theorem extractLsb'_clearStatusFlags (r : BitVec 64) (j : Nat) (hj64 : j < 64)
    (hj : (0x8D5#64).getLsbD j = false) :
    (clearStatusFlags r).extractLsb' j 1 = r.extractLsb' j 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', clearStatusFlags,
    BitVec.getLsbD_and, BitVec.getLsbD_not, Nat.add_zero, hj]
  simp [hj64]

/--
Preservation, generically: a state that agrees with a ready state except on some components
(registers, status flags, RIP, memory) and the per-step bookkeeping, and whose page tables are
intact, is ready. `ReadyToStep` reads none of the components except the page-table bytes; TF and
RF are neither status flags nor DF, so `AgreesExcept` keeps them.
-/
theorem ReadyToStep.of_agreesExcept [Bindings] {cs : List Component} {s t : RamState}
    (h : ReadyToStep s) (ha : AgreesExcept cs s t)
    (htables : IdentityPageTableMemory t.external) : ReadyToStep t := by
  have hr := ha.rest
  have e {α : Type} (f : RamState → α) (hf : ∀ u, f (fixedPart u) = f u) : f t = f s := by
    rw [← hf t, ← hf s, hr]
  have hst : SameControls s t :=
    ⟨e _ fun _ => rfl, e _ fun _ => rfl, e _ fun _ => rfl, e _ fun _ => rfl, e _ fun _ => rfl,
      e _ fun _ => rfl, e _ fun _ => rfl, e _ fun _ => rfl, e _ fun _ => rfl, e _ fun _ => rfl,
      e _ fun _ => rfl⟩
  have hflags : clearDirectionFlag (clearStatusFlags t.RFLAGS) =
      clearDirectionFlag (clearStatusFlags s.RFLAGS) :=
    congrArg (fun u => u.RFLAGS) hr
  have hc := h.cpu
  have hrd := h.ready
  refine ⟨⟨(e _ fun _ => rfl).trans hc.cs, (e _ fun _ => rfl).trans hc.ss,
      (e _ fun _ => rfl).trans hc.ds, (e _ fun _ => rfl).trans hc.es,
      (e (fun u => u.CPL) fun _ => rfl) ▸ hc.cpl, hst.cr0 ▸ hc.cr0, hst.cr4 ▸ hc.cr4,
      (e (fun u => u.IA32_EFER) fun _ => rfl) ▸ hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass,
      (e (fun u => u.DR7) fun _ => rfl) ▸ hc.debug,
      (e (fun u => u.AET_EVENT_CTRL) fun _ => rfl) ▸ hc.aet⟩,
    ⟨(e _ fun _ => rfl).trans h.memory.cr3, htables⟩,
    ⟨(e _ fun _ => rfl).trans hrd.event, (e _ fun _ => rfl).trans hrd.active,
      (e (fun u => u.Event_Blocked.STI_BLOCKING) fun _ => rfl).trans hrd.sti,
      (e (fun u => u.Event_Blocked.MOVSS_BLOCKING) fun _ => rfl).trans hrd.movss,
      (e _ fun _ => rfl).trans hrd.singleStep, (e _ fun _ => rfl).trans hrd.taskSwitch,
      (e _ fun _ => rfl).trans hrd.breakpoint, (e _ fun _ => rfl).trans hrd.busLock,
      ⟨?_⟩, ⟨?_⟩, (e _ fun _ => rfl).trans hrd.repeatClear,
      (e _ fun _ => rfl).trans hrd.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩
  · have := congrArg (fun r => r.extractLsb' 8 1) hflags
    simp only [extractLsb'_clearDirectionFlag _ 8 (by decide) (by decide),
      extractLsb'_clearStatusFlags _ 8 (by decide) (by decide)] at this
    exact this.trans hrd.tf.tf
  · have := congrArg (fun r => r.extractLsb' 16 1) hflags
    simp only [extractLsb'_clearDirectionFlag _ 16 (by decide) (by decide),
      extractLsb'_clearStatusFlags _ 16 (by decide) (by decide)] at this
    exact this.trans hrd.rf.rf

/-- The state a form starts from (after the bookkeeping reset and `k` fetches, with `Next_IP`
set) agrees with the start state everywhere. -/
theorem AgreesExcept.prepare (s : RamState) (k : Nat) (nextIP : BitVec 64) :
    AgreesExcept [] s { afterFetches (beforeFetch s) k with Next_IP := nextIP } :=
  ⟨fun c _ _ => by cases c <;> first | rfl | exact fun _ _ => rfl, fun _ _ => rfl, rfl,
    fun _ h => h⟩

/-- RIP := `Next_IP` at the end of a step changes only RIP. -/
theorem AgreesExcept.of_finishStep (t : RamState) : AgreesExcept [.rip] t (finishStep t) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, rfl, fun _ h => h⟩
  cases c with
  | rip => exact absurd (by simp) hc
  | mem a len => exact fun _ _ => rfl
  | _ => rfl

/-- A 64-bit push changes only RSP and the 8 bytes at RSP - 8 (besides the bookkeeping). -/
theorem AgreesExcept.of_pushState (t : RamState) (v : BitVec 64) :
    AgreesExcept [.reg 4, .mem (pushAddr t) 8] t (pushState t v) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => memStore_isSome _ _ _ x hx⟩
  · cases c with
    | reg r =>
      have hne : (4 : BitVec 5) ≠ r := fun h => hc (h ▸ List.mem_cons_self)
      have := Operand.read_write_reg_of_ne (m := 64)
        ((Operand.mem (pushAddr t) : Operand 64).write (stackAccess t) v) hne (pushAddr t)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => rfl
    | rip => rfl
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by simp only [pushState, Operand.write, stackAccess]) x
    | mxcsr => rfl
    | fpr x =>
      exact Component.agrees_fpr_of_fp87 (by simp only [pushState, Operand.write, stackAccess]) x
    | fsw => simp only [Component.Agrees, pushState, Operand.write, stackAccess]
    | fcc => simp only [Component.Agrees, pushState, Operand.write, stackAccess]
    | ftw => simp only [Component.Agrees, pushState, Operand.write, stackAccess]
    | fcw => simp only [Component.Agrees, pushState, Operand.write, stackAccess]
    | fpuPtr => simp only [Component.Agrees, pushState, Operand.write, stackAccess, fpuPtrOf]
    | df => exact congrArg dfBit (by simp only [pushState, Operand.write, stackAccess])
  · apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (pushAddr t) 8) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, pushState, Operand.write, stackAccess, beforeFetch, resetStepFields]

/-- A 64-bit pop into `r` changes only `r` and RSP (besides the bookkeeping). -/
theorem AgreesExcept.of_popState (t : RamState) (r : BitVec 5) :
    AgreesExcept [.reg r, .reg 4] t (popState t r) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl,
    by simp only [fixedPart, popState, Operand.write, dataAccess, beforeFetch, resetStepFields],
    fun _ h => by simpa only [popState, Operand.write, dataAccess] using h⟩
  cases c with
  | reg r' =>
    have h1 : r ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
    have h4 : (4 : BitVec 5) ≠ r' := fun h => hc (h ▸ by simp)
    have := (Operand.read_write_reg_of_ne (m := 64) _ h1
      ((Operand.mem (stackPtr t) : Operand 64).read t)).trans
      (Operand.read_write_reg_of_ne (m := 64) (dataAccess t "load") h4 (stackPtr t + 8))
    simp only [Operand.read_reg64] at this
    exact this
  | flags => rfl
  | rip => rfl
  | mem a len => exact fun _ _ => rfl
  | xmm x =>
    exact Component.agrees_xmm_of_zmm (by simp only [popState, Operand.write, dataAccess]) x
  | mxcsr => simp only [Component.Agrees, popState, Operand.write, dataAccess]
  | fpr x =>
    exact Component.agrees_fpr_of_fp87 (by simp only [popState, Operand.write, dataAccess]) x
  | fsw => simp only [Component.Agrees, popState, Operand.write, dataAccess]
  | fcc => simp only [Component.Agrees, popState, Operand.write, dataAccess]
  | ftw => simp only [Component.Agrees, popState, Operand.write, dataAccess]
  | fcw => simp only [Component.Agrees, popState, Operand.write, dataAccess]
  | fpuPtr => simp only [Component.Agrees, popState, Operand.write, dataAccess, fpuPtrOf]
  | df => simp only [Component.Agrees, popState, Operand.write, dataAccess]

/-! ### After a push step -/

/-- The state a push form starts from has the same RSP as the start state. -/
@[simp] theorem pushAddr_prepare (s : RamState) (k : Nat) (nextIP : BitVec 64) :
    pushAddr { afterFetches (beforeFetch s) k with Next_IP := nextIP } = pushAddr s := rfl

@[simp] theorem stackPtr_prepare (s : RamState) (k : Nat) (nextIP : BitVec 64) :
    stackPtr { afterFetches (beforeFetch s) k with Next_IP := nextIP } = stackPtr s := rfl

/-- After a push step, RIP is `nextIP`. -/
theorem afterStep_push_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (v nextIP : BitVec 64) :
    (afterStep s length fun t => pushState { t with Next_IP := nextIP } v).RIP = nextIP := by
  simp [afterStep, finishStep, pushState, Operand.write, stackAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Memory after a push step: the 8 bytes at RSP - 8 written. -/
@[simp] theorem afterStep_push_external (s : RamState) (length : Nat) (v nextIP : BitVec 64) :
    (afterStep s length fun t => pushState { t with Next_IP := nextIP } v).external =
      memStore s.external (pushAddr s) v := rfl

/-- After a push step, RSP is the old RSP - 8. -/
theorem Operand.read_afterStep_push_rsp (s : RamState) (length : Nat) (v nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => pushState { t with Next_IP := nextIP } v) = pushAddr s := by
  rw [Operand.read_afterStep, pushState, Operand.read_write_reg64_self]
  rfl

/-- After a push step, the 8 bytes at the old RSP - 8 hold the value pushed. -/
theorem Operand.read_afterStep_push_mem (s : RamState) (length : Nat) (v nextIP : BitVec 64) :
    (Operand.mem (pushAddr s) : Operand 64).read
      (afterStep s length fun t => pushState { t with Next_IP := nextIP } v) = v := by
  simp only [Operand.read, afterStep_push_external]
  exact memLoad_memStore _ _ (by decide) (by decide) v

/-- A push step changes only RSP, the 8 bytes at RSP - 8 and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_push (s : RamState) (length : Nat) (v nextIP : BitVec 64) :
    AgreesExcept [.reg 4, .mem (pushAddr s) 8, .rip] s
      (afterStep s length fun t => pushState { t with Next_IP := nextIP } v) :=
  ((AgreesExcept.prepare s (length + 1) nextIP).trans
    (AgreesExcept.of_pushState
      { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP } v)).trans
    (AgreesExcept.of_finishStep _)

/-- Preservation for a push: if the 8 bytes at RSP - 8 lie below 4 GiB and outside the page
tables, the state after the step is ready to step again. -/
theorem ReadyToStep.afterStep_push [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (v nextIP : BitVec 64)
    (hlow : (pushAddr s).toNat + 8 ≤ 2^32)
    (htables : PageTableEntriesApart (pushAddr s).toNat 8) :
    ReadyToStep (afterStep s length fun t => pushState { t with Next_IP := nextIP } v) :=
  h.of_agreesExcept (AgreesExcept.afterStep_push s length v nextIP) (by
    rw [afterStep_push_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables)

/-! ### After a pop step -/

/-- After a pop step, RIP is `nextIP`. -/
theorem afterStep_pop_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 5) (nextIP : BitVec 64) :
    (afterStep s length fun t => popState { t with Next_IP := nextIP } r).RIP = nextIP := by
  simp [afterStep, finishStep, popState, Operand.write, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- A pop step leaves memory unchanged. -/
@[simp] theorem afterStep_pop_external (s : RamState) (length : Nat) (r : BitVec 5)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => popState { t with Next_IP := nextIP } r).external =
      s.external := rfl

/-- After a pop step into `r`, `r` holds the 8 bytes at the old RSP. -/
theorem Operand.read_afterStep_pop (s : RamState) (length : Nat) (r : BitVec 5)
    (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read
      (afterStep s length fun t => popState { t with Next_IP := nextIP } r) =
      (Operand.mem (stackPtr s) : Operand 64).read s := by
  rw [Operand.read_afterStep, popState, Operand.read_write_reg64_self]
  rfl

/-- After a pop step into a register other than RSP, RSP is the old RSP + 8. -/
theorem Operand.read_afterStep_pop_rsp (s : RamState) (length : Nat) {r : BitVec 5}
    (hr : r ≠ 4) (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => popState { t with Next_IP := nextIP } r) = stackPtr s + 8 := by
  rw [Operand.read_afterStep, popState, Operand.read_write_reg_of_ne _ hr]
  simp [gprIndex]
  rfl

/-- A pop step into `r` changes only `r`, RSP and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_pop (s : RamState) (length : Nat) (r : BitVec 5)
    (nextIP : BitVec 64) :
    AgreesExcept [.reg r, .reg 4, .rip] s
      (afterStep s length fun t => popState { t with Next_IP := nextIP } r) :=
  ((AgreesExcept.prepare s (length + 1) nextIP).trans
    (AgreesExcept.of_popState
      { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP } r)).trans
    (AgreesExcept.of_finishStep _)

/-- Preservation for a pop. -/
theorem ReadyToStep.afterStep_pop [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 5) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => popState { t with Next_IP := nextIP } r) :=
  h.of_agreesExcept (AgreesExcept.afterStep_pop s length r nextIP) h.memory.tables

/-! ### LEAVE -/

/-- `RBP` returns register 5. -/
theorem rbp_run (s : RamState) :
    (RBP : X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run s =
      (.ok ((Operand.reg 5 : Operand 64).read s), s) := by
  simp [RBP, gprGet_eq, x86_runtime, Operand.read]
  rfl

/-- `Write_RSP` of a 64-bit value sets RSP to it. -/
theorem writeRSP64_run (u : RamState) (v : BitVec 64) :
    (Write_RSP (size := 64) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), (Operand.reg 4 : Operand 64).write u v) := by
  unfold Write_RSP
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rsp_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    pure, Except.mapError, mergeGPR64_run, mergeGPR_64]
  exact rspWrite_run u v

/-- `Write_RBP` of a 64-bit value sets RBP to it. -/
theorem writeRBP64_run (u : RamState) (v : BitVec 64) :
    (Write_RBP (size := 64) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), (Operand.reg 5 : Operand 64).write u v) := by
  unfold Write_RBP
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rbp_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError, mergeGPR64_run, mergeGPR_64,
    RBP_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp [Operand.write_reg64, gprIndex]
  rfl

/-- The state after `LEAVE` at 64 bits from `t`: RSP := RBP + 8, then RBP := the 8 bytes at the
old RBP (read by `Pop_Stack` at RBP, bookkeeping `dataAccess t "load"`). -/
def leaveState (t : RamState) : RamState :=
  (Operand.reg 5 : Operand 64).write
    ((Operand.reg 4 : Operand 64).write (dataAccess t "load")
      ((Operand.reg 5 : Operand 64).read t + 8))
    ((Operand.mem ((Operand.reg 5 : Operand 64).read t) : Operand 64).read t)

/-- `Operations.LEAVE 64`: with the 8 bytes at RBP readable, pop them as from a stack whose top
is RBP (`popStack_run`), set RSP to RBP + 8 and RBP to the value read (`leaveState`). -/
theorem leave_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hmode : In64BitMode t)
    (hr : MemReadable t ((Operand.reg 5 : Operand 64).read t) 8) :
    (X86.Instructions.Operations.LEAVE 64).run t = (.ok (), leaveState t) := by
  have hsas : (Stack_Address_Size (dataAccess t "load").SS).run (dataAccess t "load") =
      (.ok 64, dataAccess t "load") := by
    rw [show (dataAccess t "load").SS = userStackSegment from hss]
    exact stackAddressSize_run _ (hmode.of_cs_lma_eq rfl rfl)
  unfold X86.Instructions.Operations.LEAVE
  spec_run [MonadState.get => get_run _, RBP => rbp_run _,
    Pop_Stack => popStack_run t h hss _ hr, Stack_Address_Size => hsas,
    Write_RSP => writeRSP64_run _ _, Write_RBP => writeRBP64_run _ _]

/-- `LEAVE` changes only RSP and RBP (besides the bookkeeping). -/
theorem AgreesExcept.of_leaveState (t : RamState) :
    AgreesExcept [.reg 4, .reg 5] t (leaveState t) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl,
    by simp only [fixedPart, leaveState, Operand.write, dataAccess, beforeFetch, resetStepFields],
    fun _ h => by simpa only [leaveState, Operand.write, dataAccess] using h⟩
  cases c with
  | reg r' =>
    have h4 : (4 : BitVec 5) ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
    have h5 : (5 : BitVec 5) ≠ r' := fun h => hc (h ▸ by simp)
    have := (Operand.read_write_reg_of_ne (m := 64) _ h5
      ((Operand.mem ((Operand.reg 5 : Operand 64).read t) : Operand 64).read t)).trans
      (Operand.read_write_reg_of_ne (m := 64) (dataAccess t "load") h4
        ((Operand.reg 5 : Operand 64).read t + 8))
    simp only [Operand.read_reg64] at this
    exact this
  | flags => rfl
  | rip => rfl
  | mem a len => exact fun _ _ => rfl
  | xmm x =>
    exact Component.agrees_xmm_of_zmm (by simp only [leaveState, Operand.write, dataAccess]) x
  | mxcsr => simp only [Component.Agrees, leaveState, Operand.write, dataAccess]
  | fpr x =>
    exact Component.agrees_fpr_of_fp87 (by simp only [leaveState, Operand.write, dataAccess]) x
  | fsw => simp only [Component.Agrees, leaveState, Operand.write, dataAccess]
  | fcc => simp only [Component.Agrees, leaveState, Operand.write, dataAccess]
  | ftw => simp only [Component.Agrees, leaveState, Operand.write, dataAccess]
  | fcw => simp only [Component.Agrees, leaveState, Operand.write, dataAccess]
  | fpuPtr => simp only [Component.Agrees, leaveState, Operand.write, dataAccess, fpuPtrOf]
  | df => simp only [Component.Agrees, leaveState, Operand.write, dataAccess]

/-- After a `LEAVE` step, RIP is `nextIP`. -/
theorem afterStep_leave_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => leaveState { t with Next_IP := nextIP }).RIP = nextIP := by
  simp [afterStep, finishStep, leaveState, Operand.write, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- A `LEAVE` step leaves memory unchanged. -/
@[simp] theorem afterStep_leave_external (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t => leaveState { t with Next_IP := nextIP }).external =
      s.external := rfl

/-- After a `LEAVE` step, RSP is the old RBP + 8. -/
theorem Operand.read_afterStep_leave_rsp (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => leaveState { t with Next_IP := nextIP }) =
      (Operand.reg 5 : Operand 64).read s + 8 := by
  rw [Operand.read_afterStep, leaveState, Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_write_reg64_self]
  rfl

/-- After a `LEAVE` step, RBP is the 8 bytes at the old RBP. -/
theorem Operand.read_afterStep_leave_rbp (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    (Operand.reg 5 : Operand 64).read
      (afterStep s length fun t => leaveState { t with Next_IP := nextIP }) =
      (Operand.mem ((Operand.reg 5 : Operand 64).read s) : Operand 64).read s := by
  rw [Operand.read_afterStep, leaveState, Operand.read_write_reg64_self]
  rfl

/-- A `LEAVE` step changes only RSP, RBP and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_leave (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.reg 4, .reg 5, .rip] s
      (afterStep s length fun t => leaveState { t with Next_IP := nextIP }) :=
  ((AgreesExcept.prepare s (length + 1) nextIP).trans
    (AgreesExcept.of_leaveState
      { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP })).trans
    (AgreesExcept.of_finishStep _)

/-- Preservation for a `LEAVE`. -/
theorem ReadyToStep.afterStep_leave [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => leaveState { t with Next_IP := nextIP }) :=
  h.of_agreesExcept (AgreesExcept.afterStep_leave s length nextIP) h.memory.tables

/-! ### Effect and triple of a push -/

/-- The effect of a push of `v s` that continues at `rip s`: RSP set to RSP - 8 and the 8 bytes
there to `v s`. (A PUSH continues at `p + len`; a CALL will continue at its target.) -/
def pushEffect (rip : RamState → BitVec 64) (v : RamState → BitVec 64) (s : RamState) :
    Effect where
  rip := rip s
  writes := [⟨(Operand.reg 4 : Operand 64), pushAddr s⟩,
    ⟨(Operand.mem (pushAddr s) : Operand 64), v s⟩]

@[simp] theorem pushEffect_components (rip v : RamState → BitVec 64) (s : RamState) :
    (pushEffect rip v s).components = [.reg 4, .mem (pushAddr s) 8, .rip] := by
  simp [pushEffect, Effect.components]

/-- An effect that writes one register, memory bytes apart from the code, and RIP avoids the
code. -/
theorem Effect.avoids_of_components_reg_mem_rip {e : Effect} {r : BitVec 5} {a : BitVec 64}
    {len : Nat} (h : e.components = [.reg r, .mem a len, .rip]) {p : BitVec 64}
    {bytes : List UInt8} (hap : RangeApart a len p bytes.length) :
    e.Avoids (codeRange p bytes) := by
  intro x hx c hc hcov
  rw [h] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hcov
  · obtain ⟨i, hi, hxe⟩ := hcov
    obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
    exact hap i hi j hj (hxe.symm.trans hxj)
  · exact hcov

/-- A push effect avoids the instruction's code when the push precondition holds: the 8 bytes at
RSP - 8 are apart from the instruction's `len` bytes. -/
theorem pushEffect_avoids {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) (rip v : RamState → BitVec 64) {s : RamState}
    (h : PushPre p len s) : (pushEffect rip v s).Avoids (codeRange p bytes) := by
  subst hlen
  exact Effect.avoids_of_components_reg_mem_rip (pushEffect_components _ v s) h.code

/--
The step of a push form at `p` with its effect, from its step theorem. If from every ready state
with the instruction `bytes` at `p` and `PushPre`, one `step` runs the form, ending in a push of
`v s` with `Next_IP` = `p + len`, then that step reaches a ready state with the effect
`pushEffect (fun _ => p + len) v`.
-/
theorem StepEffect.of_push [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (v : RamState → BitVec 64)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → PushPre p len s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        pushState { t with Next_IP := BitVec.add p (BitVec.ofNat 64 len) } (v s)))) :
    StepEffect (PushPre p len) (codeRange p bytes)
      (pushEffect (fun _ => p + BitVec.ofNat 64 len) v) := by
  intro s h hcode hpre
  exact ⟨_, hstep s h hcode hpre,
    ReadyToStep.afterStep_push h _ _ _ hpre.write.low hpre.write.tables,
    ⟨afterStep_push_rip h _ _ _, ⟨Operand.read_afterStep_push_rsp _ _ _ _,
      Operand.read_afterStep_push_mem _ _ _ _⟩, trivial,
      (pushEffect_components _ v s).symm ▸ AgreesExcept.afterStep_push _ _ _ _⟩⟩

/--
The triple of a push form at `p`, from its step theorem (as `StepEffect.of_push`): the effect
`pushEffect (fun _ => p + len) v`, which avoids the instruction's `len` bytes
(`pushEffect_avoids`).
-/
theorem Triple.of_push [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) (v : RamState → BitVec 64)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → PushPre p len s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        pushState { t with Next_IP := BitVec.add p (BitVec.ofNat 64 len) } (v s)))) :
    Triple (PushPre p len) (codeRange p bytes)
      (Effect.post (pushEffect (fun _ => p + BitVec.ofNat 64 len) v)) :=
  Triple.of_effect (fun _ hpre => pushEffect_avoids hlen _ v hpre) (StepEffect.of_push v hstep)

/-! ### 16-bit pushes and pops (`66` prefix) -/

/-- `linearAddressFromOracle` for a 2-byte access (a 16-bit push). -/
noncomputable def linearAddressFromOracle2 (o : X86.Runtime.Oracle) (ds : Segment) (cpl : Int)
    (address : BitVec 64) : Address_Translation × X86.Runtime.Oracle :=
  let (offset, o) := o.take 64
  let (pa1, o) := o.take 64
  let (tr1, o) := translationFromOracle o address pa1 .Memory_Type_Unknown
  let (pa2, o) := o.take 64
  let (tr2, o) := translationFromOracle o address pa2 .Memory_Type_Unknown
  ({ num_bytes := 2, segment := nullDataSegment ds, offset := offset,
     linear_address := address, is_implicit_supervisor_mode_access := false,
     is_shadow_stack_access := false, translation_cpl := cpl,
     is_split_access := false, translation1 := tr1, translation2 := tr2 }, o)

/-- `Create_Linear_Address` for 2 bytes draws 336 oracle bits, as for 8. -/
theorem linearAddressFromOracle2_oracle (o : X86.Runtime.Oracle) (ds : Segment) (cpl : Int)
    (address : BitVec 64) :
    (linearAddressFromOracle2 o ds cpl address).2 = oracleSkip o 336 := by
  simp [linearAddressFromOracle2, translationFromOracle, oracleTake_snd, oracleSkip_oracleSkip]

/-- `Create_Linear_Address` for 2 bytes in 64-bit mode (EFER.LMA = 1), as
`createLinearAddress64_run`. -/
theorem createLinearAddress16_run (s : RamState) (address : BitVec 64)
    (hlma : s.IA32_EFER.LMA = 1) :
    (Create_Linear_Address address 16).run s =
      (.ok (linearAddressFromOracle2 s.oracle s.DS s.CPL address).1,
        { s with oracle := oracleSkip s.oracle 336 }) := by
  rw [← linearAddressFromOracle2_oracle s.oracle s.DS s.CPL address]
  unfold Create_Linear_Address
  spec_run [MonadState.get => get_run _]
  dsimp only
  rw [hlma]
  spec_run [MonadState.get => get_run _, Create_Translation => createTranslation_run _ _ _]

/-- `Push_Stack` of a 16-bit value (`pushStack_run` for 2 bytes): writes `v` at `rsp - 2` and
returns `rsp - 2`. -/
theorem pushStack16_run [Bindings] (s : RamState) (h : DataReady s) (hss : s.SS = userStackSegment)
    (rsp : BitVec 64) (v : BitVec 16) (hw : MemWritable s (rsp - 2) 2) :
    (Push_Stack s.SS rsp s.CS 16 16 v).run s =
      (.ok (rsp - 2 : BitVec 64),
        (Operand.mem (rsp - 2) : Operand 16).write (stackAccess s) v) := by
  let t : RamState := { s with oracle := oracleSkip s.oracle 336 }
  have ht : DataReady t := h.oracle _
  have hcan := isCanonicalWrtPagingMode_run s (rsp - 2) 2 h.cr0 h.cr4 h.efer.lme h.lam
    (by have := hw.low; omega) hw.low
  let linear : Address_Translation :=
    { (linearAddressFromOracle2 s.oracle s.DS s.CPL (rsp - 2)).1 with
      translation_cpl := X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) }
  have htr := translateLinearToPhysical_run_of_dataReady t ht linear .Memory_Write 2 rfl
    (by decide) rfl hw.low
  have hcpl : 0 ≤ X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ∧
      X86.Runtime.Unsigned (Segment_Selector.RPL userCodeSegment.selector) ≤ 3 := by decide
  have hphys := physicalMemWrite_dataPhysical_run linear (rsp - 2) rfl 16 (by decide) rfl v t
    ht.smrr hcpl hw.mem
  unfold Push_Stack
  rw [hss, h.cs]
  spec_run [MonadState.get => get_run _,
    Is_64Bit_Code_Segment => is64BitCodeSegment_userCodeSegment_run _ h.efer.lma,
    Is_Canonical_Wrt_Paging_Mode => hcan,
    Create_Linear_Address => createLinearAddress16_run _ _ h.efer.lma,
    Is_Alignment_Checking_Enabled => isAlignmentCheckingEnabled_run _ ht.cr0,
    Check_Write_Permission => checkWritePermission_run _ _ ht.cs ht.efer.lma,
    Check_Data_Write_Breakpoint => checkDataWriteBreakpoint_run _ _ _ ht.debug,
    Translate_Linear_To_Physical.interpreted => htr,
    Physical_Mem_Write => hphys]

/-- `Pop_Stack` of 16 bits (`popStack_run` for 2 bytes): returns the 2 bytes at `rsp` and
`rsp + 2`. -/
theorem popStack16_run [Bindings] (s : RamState) (h : DataReady s) (hss : s.SS = userStackSegment)
    (rsp : BitVec 64) (hr : MemReadable s rsp 2) :
    (Pop_Stack s.SS rsp 16 16).run s =
      (.ok ((Operand.mem rsp : Operand 16).read s, (rsp + 2 : BitVec 64)),
        dataAccess s "load") := by
  have hread := logicalMemRead_run s h true rsp 16 (by decide) .Memory_Read (.inl rfl)
    hr.low hr.mem
  have hmode := in64BitMode_of_userCodeSegment h.cs h.efer.lma
  unfold Pop_Stack
  rw [hss]
  simp only [show (0 : Int) ≤ 16 from by decide, decide_true, beq_self_eq_true, Bool.true_or,
    assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (s := s) (t := s) (value := true) rfl).trans ?_
  refine (specM_bind_run _ _ (s := s) (t := s) (value := ()) rfl).trans ?_
  refine (specM_bind_run _ _ (stackAddressSize_run s hmode)).trans ?_
  refine (specM_bind_run (Std.Integer.Positive_Divide 16 8 :
    X86.Runtime.SpecM X86.Exception RamState Int) _ (s := s) rfl).trans ?_
  refine (specM_bind_run _ _ hmode).trans ?_
  refine (specM_bind_run (liftM (Null_Segment userStackSegment)) _ (s := s) (t := s)
    (value := flatData true) rfl).trans ?_
  refine (specM_bind_run (X86.Runtime.CheckedSlice.read rsp 0 64) _ (s := s) (t := s)
    (value := rsp) (checkedSliceRead_full_run s rsp)).trans ?_
  refine (specM_bind_run (Std.Bits.Zero_Extend (source_size := 64) rsp 64) _ (s := s) (t := s)
    (value := rsp) (zeroExtend_full_run s rsp)).trans ?_
  refine (specM_bind_run _ _ hread).trans ?_
  refine (specM_bind_run _ _ (s := dataAccess s "load") (t := dataAccess s "load")
    (value := (rsp + 2 : BitVec 64)) rfl).trans ?_
  simp only [show ((64 : Int) == 16) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (checkedSliceRead_full_run _ _)).trans ?_
  exact (specM_bind_run _ _ (zeroExtend_full_run _ _)).trans rfl

/-- The address a 16-bit push writes: RSP - 2. -/
def pushAddr16 (s : RamState) : BitVec 64 := stackPtr s - 2

/-- The state after a 16-bit push of `v` from `t`: the 2 bytes at RSP - 2 hold `v`, RSP is
RSP - 2, plus the bookkeeping (`stackAccess`). -/
def pushState16 (t : RamState) (v : BitVec 16) : RamState :=
  (Operand.reg 4 : Operand 64).write
    ((Operand.mem (pushAddr16 t) : Operand 16).write (stackAccess t) v) (pushAddr16 t)

/-- The state after a 16-bit pop into register `r` from `t`: RSP is RSP + 2, then the low 16 bits
of `r` are the 2 bytes at the old RSP. -/
def popState16 (t : RamState) (r : BitVec 5) : RamState :=
  (Operand.reg r : Operand 16).write
    ((Operand.reg 4 : Operand 64).write (dataAccess t "load") (stackPtr t + 2))
    ((Operand.mem (stackPtr t) : Operand 16).read t)

/-- `Operations.PUSH 16 v`: with RSP - 2 writable, the push is `pushState16`. -/
theorem push16_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (v : BitVec 16) (hw : MemWritable t (pushAddr16 t) 2) :
    (X86.Instructions.Operations.PUSH 16 v).run t = (.ok (), pushState16 t v) := by
  unfold X86.Instructions.Operations.PUSH
  spec_run [MonadState.get => get_run _, RSP => rsp_run _,
    Push_Stack => pushStack16_run t h hss (stackPtr t) v hw, RSP_write => rspWrite_run _ _]

/-- `Operations.POP 16`: with the 2 bytes at RSP readable, the pop returns them and the new stack
pointer RSP + 2, which the form writes. -/
theorem pop16_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 2) :
    (X86.Instructions.Operations.POP 16).run t =
      (.ok ((Operand.mem (stackPtr t) : Operand 16).read t, (stackPtr t + 2 : BitVec 64)),
        dataAccess t "load") := by
  unfold X86.Instructions.Operations.POP
  spec_run [MonadState.get => get_run _, RSP => rsp_run _,
    Pop_Stack => popStack16_run t h hss (stackPtr t) hr]

/-- A 16-bit push changes only RSP and the 2 bytes at RSP - 2 (besides the bookkeeping). -/
theorem AgreesExcept.of_pushState16 (t : RamState) (v : BitVec 16) :
    AgreesExcept [.reg 4, .mem (pushAddr16 t) 2] t (pushState16 t v) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => memStore_isSome _ _ _ x hx⟩
  · cases c with
    | reg r =>
      have hne : (4 : BitVec 5) ≠ r := fun h => hc (h ▸ List.mem_cons_self)
      have := Operand.read_write_reg_of_ne (m := 64)
        ((Operand.mem (pushAddr16 t) : Operand 16).write (stackAccess t) v) hne (pushAddr16 t)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => rfl
    | rip => rfl
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by simp only [pushState16, Operand.write, stackAccess]) x
    | mxcsr => rfl
    | fpr x =>
      exact Component.agrees_fpr_of_fp87 (by simp only [pushState16, Operand.write, stackAccess]) x
    | fsw => simp only [Component.Agrees, pushState16, Operand.write, stackAccess]
    | fcc => simp only [Component.Agrees, pushState16, Operand.write, stackAccess]
    | ftw => simp only [Component.Agrees, pushState16, Operand.write, stackAccess]
    | fcw => simp only [Component.Agrees, pushState16, Operand.write, stackAccess]
    | fpuPtr => simp only [Component.Agrees, pushState16, Operand.write, stackAccess, fpuPtrOf]
    | df => exact congrArg dfBit (by simp only [pushState16, Operand.write, stackAccess])
  · apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (pushAddr16 t) 2) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, pushState16, Operand.write, stackAccess, beforeFetch, resetStepFields]

/-- A 16-bit pop into `r` changes only `r` and RSP (besides the bookkeeping). -/
theorem AgreesExcept.of_popState16 (t : RamState) (r : BitVec 5) :
    AgreesExcept [.reg r, .reg 4] t (popState16 t r) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl,
    by simp only [fixedPart, popState16, Operand.write, dataAccess, beforeFetch, resetStepFields],
    fun _ h => by simpa only [popState16, Operand.write, dataAccess] using h⟩
  cases c with
  | reg r' =>
    have h1 : r ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
    have h4 : (4 : BitVec 5) ≠ r' := fun h => hc (h ▸ by simp)
    have := (Operand.read_write_reg_of_ne (m := 64) _ h1
      ((Operand.mem (stackPtr t) : Operand 16).read t)).trans
      (Operand.read_write_reg_of_ne (m := 64) (dataAccess t "load") h4 (stackPtr t + 2))
    simp only [Operand.read_reg64] at this
    exact this
  | flags => rfl
  | rip => rfl
  | mem a len => exact fun _ _ => rfl
  | xmm x =>
    exact Component.agrees_xmm_of_zmm (by simp only [popState16, Operand.write, dataAccess]) x
  | mxcsr => simp only [Component.Agrees, popState16, Operand.write, dataAccess]
  | fpr x =>
    exact Component.agrees_fpr_of_fp87 (by simp only [popState16, Operand.write, dataAccess]) x
  | fsw => simp only [Component.Agrees, popState16, Operand.write, dataAccess]
  | fcc => simp only [Component.Agrees, popState16, Operand.write, dataAccess]
  | ftw => simp only [Component.Agrees, popState16, Operand.write, dataAccess]
  | fcw => simp only [Component.Agrees, popState16, Operand.write, dataAccess]
  | fpuPtr => simp only [Component.Agrees, popState16, Operand.write, dataAccess, fpuPtrOf]
  | df => simp only [Component.Agrees, popState16, Operand.write, dataAccess]

/-- After a 16-bit push step, RIP is `nextIP`. -/
theorem afterStep_push16_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (v : BitVec 16) (nextIP : BitVec 64) :
    (afterStep s length fun t => pushState16 { t with Next_IP := nextIP } v).RIP = nextIP := by
  simp [afterStep, finishStep, pushState16, Operand.write, stackAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- Memory after a 16-bit push step: the 2 bytes at RSP - 2 written. -/
@[simp] theorem afterStep_push16_external (s : RamState) (length : Nat) (v : BitVec 16)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => pushState16 { t with Next_IP := nextIP } v).external =
      memStore s.external (pushAddr16 s) v := rfl

/-- After a 16-bit push step, RSP is the old RSP - 2. -/
theorem Operand.read_afterStep_push16_rsp (s : RamState) (length : Nat) (v : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => pushState16 { t with Next_IP := nextIP } v) = pushAddr16 s := by
  rw [Operand.read_afterStep, pushState16, Operand.read_write_reg64_self]
  rfl

/-- After a 16-bit push step, the 2 bytes at the old RSP - 2 hold the value pushed. -/
theorem Operand.read_afterStep_push16_mem (s : RamState) (length : Nat) (v : BitVec 16)
    (nextIP : BitVec 64) :
    (Operand.mem (pushAddr16 s) : Operand 16).read
      (afterStep s length fun t => pushState16 { t with Next_IP := nextIP } v) = v := by
  simp only [Operand.read, afterStep_push16_external]
  exact memLoad_memStore _ _ (by decide) (by decide) v

/-- A 16-bit push step changes only RSP, the 2 bytes at RSP - 2 and RIP. -/
theorem AgreesExcept.afterStep_push16 (s : RamState) (length : Nat) (v : BitVec 16)
    (nextIP : BitVec 64) :
    AgreesExcept [.reg 4, .mem (pushAddr16 s) 2, .rip] s
      (afterStep s length fun t => pushState16 { t with Next_IP := nextIP } v) :=
  ((AgreesExcept.prepare s (length + 1) nextIP).trans
    (AgreesExcept.of_pushState16
      { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP } v)).trans
    (AgreesExcept.of_finishStep _)

/-- Preservation for a 16-bit push. -/
theorem ReadyToStep.afterStep_push16 [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (v : BitVec 16) (nextIP : BitVec 64)
    (hlow : (pushAddr16 s).toNat + 2 ≤ 2^32)
    (htables : PageTableEntriesApart (pushAddr16 s).toNat 2) :
    ReadyToStep (afterStep s length fun t => pushState16 { t with Next_IP := nextIP } v) :=
  h.of_agreesExcept (AgreesExcept.afterStep_push16 s length v nextIP) (by
    rw [afterStep_push16_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hlow htables)

/-- After a 16-bit pop step, RIP is `nextIP`. -/
theorem afterStep_pop16_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 5) (nextIP : BitVec 64) :
    (afterStep s length fun t => popState16 { t with Next_IP := nextIP } r).RIP = nextIP := by
  simp [afterStep, finishStep, popState16, Operand.write, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After a 16-bit pop step into `r`, `r` holds the 2 bytes at the old RSP merged into its low
16 bits (for `r` not RSP). -/
theorem Operand.read_afterStep_pop16 (s : RamState) (length : Nat) {r : BitVec 5} (hr : r ≠ 4)
    (nextIP : BitVec 64) :
    (Operand.reg r : Operand 64).read
      (afterStep s length fun t => popState16 { t with Next_IP := nextIP } r) =
      mergeGPR 16 ((Operand.mem (stackPtr s) : Operand 16).read s)
        ((Operand.reg r : Operand 64).read s) := by
  have hm (X : RamState) (v : BitVec 16) :
      (Operand.reg r : Operand 64).read ((Operand.reg r : Operand 16).write X v) =
        mergeGPR 16 v ((Operand.reg r : Operand 64).read X) := by
    simp [Operand.write, Operand.read]
  rw [Operand.read_afterStep, popState16, hm, Operand.read_write_reg_of_ne _ (Ne.symm hr)]
  rfl

/-- After a 16-bit pop step into a register other than RSP, RSP is the old RSP + 2. -/
theorem Operand.read_afterStep_pop16_rsp (s : RamState) (length : Nat) {r : BitVec 5}
    (hr : r ≠ 4) (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => popState16 { t with Next_IP := nextIP } r) = stackPtr s + 2 := by
  rw [Operand.read_afterStep, popState16, Operand.read_write_reg_of_ne _ hr]
  simp [gprIndex]
  rfl

/-- A 16-bit pop step into `r` changes only `r`, RSP and RIP. -/
theorem AgreesExcept.afterStep_pop16 (s : RamState) (length : Nat) (r : BitVec 5)
    (nextIP : BitVec 64) :
    AgreesExcept [.reg r, .reg 4, .rip] s
      (afterStep s length fun t => popState16 { t with Next_IP := nextIP } r) :=
  ((AgreesExcept.prepare s (length + 1) nextIP).trans
    (AgreesExcept.of_popState16
      { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP } r)).trans
    (AgreesExcept.of_finishStep _)

/-- Preservation for a 16-bit pop. -/
theorem ReadyToStep.afterStep_pop16 [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 5) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => popState16 { t with Next_IP := nextIP } r) :=
  h.of_agreesExcept (AgreesExcept.afterStep_pop16 s length r nextIP) h.memory.tables

/-! ### 16-bit LEAVE (`66 C9`) -/

/-- `Write_RBP` of a 16-bit value replaces the low 16 bits of RBP, keeping the bits above. -/
theorem writeRBP16_run (u : RamState) (v : BitVec 16) :
    (Write_RBP (size := 16) v : X86.Runtime.SpecM X86.Exception RamState Unit).run u =
      (.ok (), (Operand.reg 5 : Operand 16).write u v) := by
  unfold Write_RBP
  simp only [x86_runtime, pure_bind]
  rw [specM_bind_run _ _ (rbp_run u)]
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, Functor.map, pure, Except.mapError,
    mergeGPR_run 16 (by decide) v ((Operand.reg 5 : Operand 64).read u),
    RBP_write, gprSet_eq, x86_runtime, modify, modifyGet, MonadStateOf.modifyGet]
  simp [Operand.write_reg16, gprIndex]
  rfl

/-- The state after `LEAVE` at 16 bits from `t`: RSP := RBP + 2, then the low 16 bits of RBP :=
the 2 bytes at the old RBP (read by `Pop_Stack` at RBP, bookkeeping `dataAccess t "load"`). -/
def leaveState16 (t : RamState) : RamState :=
  (Operand.reg 5 : Operand 16).write
    ((Operand.reg 4 : Operand 64).write (dataAccess t "load")
      ((Operand.reg 5 : Operand 64).read t + 2))
    ((Operand.mem ((Operand.reg 5 : Operand 64).read t) : Operand 16).read t)

/-- `Operations.LEAVE 16`: with the 2 bytes at RBP readable, pop them as from a stack whose top
is RBP (`popStack16_run`), set RSP to RBP + 2 and the low 16 bits of RBP to the value read
(`leaveState16`). -/
theorem leave16_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hmode : In64BitMode t)
    (hr : MemReadable t ((Operand.reg 5 : Operand 64).read t) 2) :
    (X86.Instructions.Operations.LEAVE 16).run t = (.ok (), leaveState16 t) := by
  have hsas : (Stack_Address_Size (dataAccess t "load").SS).run (dataAccess t "load") =
      (.ok 64, dataAccess t "load") := by
    rw [show (dataAccess t "load").SS = userStackSegment from hss]
    exact stackAddressSize_run _ (hmode.of_cs_lma_eq rfl rfl)
  unfold X86.Instructions.Operations.LEAVE
  spec_run [MonadState.get => get_run _, RBP => rbp_run _,
    Pop_Stack => popStack16_run t h hss _ hr, Stack_Address_Size => hsas,
    Write_RSP => writeRSP64_run _ _, Write_RBP => writeRBP16_run _ _]

/-- A 16-bit `LEAVE` changes only RSP and RBP (besides the bookkeeping). -/
theorem AgreesExcept.of_leaveState16 (t : RamState) :
    AgreesExcept [.reg 4, .reg 5] t (leaveState16 t) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl,
    by simp only [fixedPart, leaveState16, Operand.write, dataAccess, beforeFetch, resetStepFields],
    fun _ h => by simpa only [leaveState16, Operand.write, dataAccess] using h⟩
  cases c with
  | reg r' =>
    have h4 : (4 : BitVec 5) ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
    have h5 : (5 : BitVec 5) ≠ r' := fun h => hc (h ▸ by simp)
    have := (Operand.read_write_reg_of_ne (m := 64) _ h5
      ((Operand.mem ((Operand.reg 5 : Operand 64).read t) : Operand 16).read t)).trans
      (Operand.read_write_reg_of_ne (m := 64) (dataAccess t "load") h4
        ((Operand.reg 5 : Operand 64).read t + 2))
    simp only [Operand.read_reg64] at this
    exact this
  | flags => rfl
  | rip => rfl
  | mem a len => exact fun _ _ => rfl
  | xmm x =>
    exact Component.agrees_xmm_of_zmm (by simp only [leaveState16, Operand.write, dataAccess]) x
  | mxcsr => simp only [Component.Agrees, leaveState16, Operand.write, dataAccess]
  | fpr x =>
    exact Component.agrees_fpr_of_fp87 (by simp only [leaveState16, Operand.write, dataAccess]) x
  | fsw => simp only [Component.Agrees, leaveState16, Operand.write, dataAccess]
  | fcc => simp only [Component.Agrees, leaveState16, Operand.write, dataAccess]
  | ftw => simp only [Component.Agrees, leaveState16, Operand.write, dataAccess]
  | fcw => simp only [Component.Agrees, leaveState16, Operand.write, dataAccess]
  | fpuPtr => simp only [Component.Agrees, leaveState16, Operand.write, dataAccess, fpuPtrOf]
  | df => simp only [Component.Agrees, leaveState16, Operand.write, dataAccess]

/-- After a 16-bit `LEAVE` step, RIP is `nextIP`. -/
theorem afterStep_leave16_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (nextIP : BitVec 64) :
    (afterStep s length fun t => leaveState16 { t with Next_IP := nextIP }).RIP = nextIP := by
  simp [afterStep, finishStep, leaveState16, Operand.write, dataAccess, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- A 16-bit `LEAVE` step leaves memory unchanged. -/
@[simp] theorem afterStep_leave16_external (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    (afterStep s length fun t => leaveState16 { t with Next_IP := nextIP }).external =
      s.external := rfl

/-- After a 16-bit `LEAVE` step, RSP is the old RBP + 2. -/
theorem Operand.read_afterStep_leave16_rsp (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    (Operand.reg 4 : Operand 64).read
      (afterStep s length fun t => leaveState16 { t with Next_IP := nextIP }) =
      (Operand.reg 5 : Operand 64).read s + 2 := by
  rw [Operand.read_afterStep, leaveState16, Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_write_reg64_self]
  rfl

/-- After a 16-bit `LEAVE` step, RBP is the 2 bytes at the old RBP merged into its low 16 bits. -/
theorem Operand.read_afterStep_leave16_rbp (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    (Operand.reg 5 : Operand 64).read
      (afterStep s length fun t => leaveState16 { t with Next_IP := nextIP }) =
      mergeGPR 16 ((Operand.mem ((Operand.reg 5 : Operand 64).read s) : Operand 16).read s)
        ((Operand.reg 5 : Operand 64).read s) := by
  have hm (X : RamState) (v : BitVec 16) :
      (Operand.reg 5 : Operand 64).read ((Operand.reg 5 : Operand 16).write X v) =
        mergeGPR 16 v ((Operand.reg 5 : Operand 64).read X) := by
    simp [Operand.write, Operand.read]
  rw [Operand.read_afterStep, leaveState16, hm, Operand.read_write_reg_of_ne _ (by decide)]
  rfl

/-- A 16-bit `LEAVE` step changes only RSP, RBP and RIP (besides the bookkeeping). -/
theorem AgreesExcept.afterStep_leave16 (s : RamState) (length : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.reg 4, .reg 5, .rip] s
      (afterStep s length fun t => leaveState16 { t with Next_IP := nextIP }) :=
  ((AgreesExcept.prepare s (length + 1) nextIP).trans
    (AgreesExcept.of_leaveState16
      { afterFetches (beforeFetch s) (length + 1) with Next_IP := nextIP })).trans
    (AgreesExcept.of_finishStep _)

/-- Preservation for a 16-bit `LEAVE`. -/
theorem ReadyToStep.afterStep_leave16 [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => leaveState16 { t with Next_IP := nextIP }) :=
  h.of_agreesExcept (AgreesExcept.afterStep_leave16 s length nextIP) h.memory.tables

/-- The precondition of a 16-bit push triple at `p`, for an instruction of `codeLen` bytes: RIP =
`p`, and the 2 bytes at RSP - 2 can be written in place and miss the instruction's bytes. -/
abbrev Push16Pre (p : BitVec 64) (codeLen : Nat) : RamState → Prop :=
  StorePre p codeLen pushAddr16 2

/-- The precondition of a 16-bit pop triple at `p`: RIP = `p`, and the 2 bytes at RSP can be
read. -/
abbrev Pop16Pre (p : BitVec 64) : RamState → Prop :=
  LoadPre p stackPtr 2

/-- The effect of a 16-bit push of `v s` that continues at `rip s`: RSP set to RSP - 2 and the 2
bytes there to `v s`. -/
def push16Effect (rip : RamState → BitVec 64) (v : RamState → BitVec 16) (s : RamState) :
    Effect where
  rip := rip s
  writes := [⟨(Operand.reg 4 : Operand 64), pushAddr16 s⟩,
    ⟨(Operand.mem (pushAddr16 s) : Operand 16), v s⟩]

@[simp] theorem push16Effect_components (rip : RamState → BitVec 64) (v : RamState → BitVec 16)
    (s : RamState) : (push16Effect rip v s).components = [.reg 4, .mem (pushAddr16 s) 2, .rip] := by
  simp [push16Effect, Effect.components]

/-- A 16-bit push effect avoids the instruction's code when the push precondition holds. -/
theorem push16Effect_avoids {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (hlen : bytes.length = len) (rip : RamState → BitVec 64) (v : RamState → BitVec 16)
    {s : RamState} (h : Push16Pre p len s) : (push16Effect rip v s).Avoids (codeRange p bytes) := by
  subst hlen
  exact Effect.avoids_of_components_reg_mem_rip (push16Effect_components _ v s) h.code

/-- The step of a 16-bit push form at `p` with its effect, from its step theorem (as
`StepEffect.of_push`). -/
theorem StepEffect.of_push16 [Bindings] {p : BitVec 64} {bytes : List UInt8} {len : Nat}
    (v : RamState → BitVec 16)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → Push16Pre p len s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        pushState16 { t with Next_IP := BitVec.add p (BitVec.ofNat 64 len) } (v s)))) :
    StepEffect (Push16Pre p len) (codeRange p bytes)
      (push16Effect (fun _ => p + BitVec.ofNat 64 len) v) := by
  intro s h hcode hpre
  exact ⟨_, hstep s h hcode hpre,
    ReadyToStep.afterStep_push16 h _ _ _ hpre.write.low hpre.write.tables,
    ⟨afterStep_push16_rip h _ _ _, ⟨Operand.read_afterStep_push16_rsp _ _ _ _,
      Operand.read_afterStep_push16_mem _ _ _ _⟩, trivial,
      (push16Effect_components _ v s).symm ▸ AgreesExcept.afterStep_push16 _ _ _ _⟩⟩

/-! ### Stack addresses as reads (for composing blocks) -/

@[x86_compose, x86_pre_simp] theorem stackPtr_eq_read (t : RamState) :
    stackPtr t = (Operand.reg 4 : Operand 64).read t := by
  simp [stackPtr]

@[x86_pre_simp] theorem pushAddr_eq_read (t : RamState) :
    pushAddr t = (Operand.reg 4 : Operand 64).read t + 0xFFFFFFFFFFFFFFF8#64 := by
  simp only [pushAddr, stackPtr, Operand.read_reg64, BitVec.sub_eq_add_neg]
  rfl

@[x86_pre_simp] theorem pushAddr16_eq_read (t : RamState) :
    pushAddr16 t = (Operand.reg 4 : Operand 64).read t + 0xFFFFFFFFFFFFFFFE#64 := by
  simp only [pushAddr16, stackPtr, Operand.read_reg64, BitVec.sub_eq_add_neg]
  rfl

attribute [x86_addr] stackPtr pushAddr pushAddr16

attribute [x86_compose] pushEffect push16Effect

end X86Proofs
