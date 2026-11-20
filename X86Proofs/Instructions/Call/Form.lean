import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Instructions.Branch.Form

/-!
# Layer 2: CALL and RET forms

lean-x86's near call (`Operations.CALL_NEAR`) computes the target, asks whether the CET shadow
stack is on (`isShadowStackEnabled_run`: no), checks the target (`Check_New_RIP`:
`checkNewRIP_run`, below 4 GiB), pushes `Next_IP` (`Push_Stack`: `pushStack_run`), sets RSP,
branches (RIP := target, `Branch_Taken`) and asks whether CET end-branch tracking is on
(`isEndBranchEnabledAndNotSuppressed_run`: no). The near return (`Operations.RET_NEAR`) pops 8 bytes
(`popStack_run`), skips the shadow stack, checks and branches to them, and sets RSP to the popped
RSP + 0 (the `imm16` of `C2`, here 0).

Results:
- `callState t ret target`: `pushState t ret` (the 8 bytes at RSP - 8 := `ret`, RSP := RSP - 8)
  with RIP := `target` and `Branch_Taken`.
- `retState t`: the pop's bookkeeping (`dataAccess t "load"`), RIP := `stackTop t` (the 8 bytes
  at RSP), `Branch_Taken`, RSP := RSP + 8.

Operation lemmas: `call_operation_rel` (relative, `E8`), `call_operation_abs` (absolute, indirect:
`FF /2`), `ret_operation`, and `ret_imm_operation` (`C2 iw`: RSP := RSP + 8 + `imm`, the state
`retImmState`; for the generated `Instructions/Ret`). Form lemmas: `call_rel32_form` (`E8 rel32`),
`call_r_form` (`FF /2` register), `call_m_seg_form` (`FF /2` memory; the address
computation as a hypothesis, any segment, the pointer read at its linear address, as for
`mov_r_m_form`) and `call_m_form` (its flat-segment case), `ret_form` (`C3`).

These are stepped by hand (`spec_bind_with` with explicit lemmas and `get_run`): `spec_run`'s
`rfl` steps over `get` and over `CheckedSlice.read`/`Sign_Extend` leave the kernel to rediscover
states and values (`extractLsb' 0 64 x` for `x`), and it times out.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The state after a near call from `t` that pushes `ret` and branches to `target`. -/
def callState (t : RamState) (ret target : BitVec 64) : RamState :=
  { pushState t ret with RIP := target, Branch_Taken := true }

/-- A state ready for data accesses has what a taken branch's checks need. -/
theorem DataReady.branchReady [Bindings] {t : RamState} (h : DataReady t) : BranchReady t :=
  ⟨h.cs, h.efer.lma, h.cpl, h.cr0, h.cr4, h.efer.lme, h.lam⟩

/-- `Branch_Near`: RIP := `target` and `Branch_Taken`. -/
theorem branchNear_run {σ : Type} (t : X86.State σ) (target : BitVec 64) :
    (Branch_Near target).run t = (.ok (), { t with RIP := target, Branch_Taken := true }) := rfl

/-- `Operations.CALL_NEAR 64` relative (`E8`), from `t` with `Next_IP` set: push `Next_IP`, branch
to `Next_IP + off`. Needs the target below 4 GiB and the 8 bytes at RSP - 8 writable in place. -/
theorem call_operation_rel [Bindings] (t : RamState) (ctx : Instruction_Context) (off : BitVec 64)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hmode : In64BitMode t)
    (htarget : (BitVec.add t.Next_IP off).toNat < 2^32) (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.Operations.CALL_NEAR 64 ctx off true false false).run t =
      (.ok (), callState t t.Next_IP (BitVec.add t.Next_IP off)) := by
  have hb := h.branchReady
  have hend := isEndBranchEnabledAndNotSuppressed_run
    ({ (Operand.reg 4 : Operand 64).write ((Operand.mem (stackPtr t - 8) : Operand 64).write
      (stackAccess t) t.Next_IP)
      (stackPtr t - 8) with RIP := BitVec.add t.Next_IP off, Branch_Taken := true } : RamState)
    (by dsimp only [Operand.write, stackAccess]; exact h.cpl)
    (by dsimp only [Operand.write, stackAccess]; exact h.cr4)
  unfold X86.Instructions.Operations.CALL_NEAR
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (signExtend64_run off t)
  spec_bind_with (relativeBranchWrap_run t _ _ hmode)
  repeat spec_bind_rfl
  spec_bind_with (isShadowStackEnabled_run t h.cpl h.cr4)
  spec_bind_rfl
  simp only [HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.not_false, ↓reduceIte]
  spec_bind_with (get_run t)
  spec_bind_with (checkNewRIP_run t _ hb htarget)
  spec_bind_with (get_run t)
  spec_bind_with (rsp_run t)
  spec_bind_with (get_run t)
  refine (specM_bind_run _ _ (s := t) (t := t) (value := t.Next_IP)
    ((specM_bind_run _ _ rfl).trans ((specM_bind_run _ _ (get_run t)).trans
      (checkedSliceRead_full_run t t.Next_IP)))).trans ?_
  spec_bind_with (pushStack_run t h hss (stackPtr t) t.Next_IP hw)
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (rspWrite_run _ _)
  spec_bind_with (branchNear_run _ _)
  spec_bind_with (get_run _)
  spec_bind_with hend
  rfl

/-- `Operations.CALL_NEAR 64` absolute and indirect (`FF /2`), from `t` with `Next_IP` set: push
`Next_IP`, branch to `target`. -/
theorem call_operation_abs [Bindings] (t : RamState) (ctx : Instruction_Context)
    (target : BitVec 64) (noTrack : Bool)
    (h : DataReady t) (hss : t.SS = userStackSegment)
    (htarget : target.toNat < 2^32) (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.Operations.CALL_NEAR 64 ctx target false true noTrack).run t =
      (.ok (), callState t t.Next_IP target) := by
  have hb := h.branchReady
  have hend := isEndBranchEnabledAndNotSuppressed_run
    ({ (Operand.reg 4 : Operand 64).write ((Operand.mem (stackPtr t - 8) : Operand 64).write
      (stackAccess t) t.Next_IP)
      (stackPtr t - 8) with RIP := target, Branch_Taken := true } : RamState)
    (by dsimp only [Operand.write, stackAccess]; exact h.cpl)
    (by dsimp only [Operand.write, stackAccess]; exact h.cr4)
  unfold X86.Instructions.Operations.CALL_NEAR
  spec_bind_rfl
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (zeroExtend_full_run t target)
  spec_bind_with (get_run t)
  spec_bind_with (isShadowStackEnabled_run t h.cpl h.cr4)
  spec_bind_rfl
  simp only [HAnd.hAnd, AndOp.and, strictAnd, Bool.false_and, Bool.not_false, ↓reduceIte]
  spec_bind_with (get_run t)
  spec_bind_with (checkNewRIP_run t _ hb htarget)
  spec_bind_with (get_run t)
  spec_bind_with (rsp_run t)
  spec_bind_with (get_run t)
  refine (specM_bind_run _ _ (s := t) (t := t) (value := t.Next_IP)
    ((specM_bind_run _ _ rfl).trans ((specM_bind_run _ _ (get_run t)).trans
      (checkedSliceRead_full_run t t.Next_IP)))).trans ?_
  spec_bind_with (pushStack_run t h hss (stackPtr t) t.Next_IP hw)
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (rspWrite_run _ _)
  spec_bind_with (branchNear_run _ _)
  spec_bind_with (get_run _)
  spec_bind_with hend
  simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The 8 bytes at RSP: what a `ret` pops. -/
def stackTop (t : RamState) : BitVec 64 := (Operand.mem (stackPtr t) : Operand 64).read t

/-- The state after a near return from `t`: RIP := `stackTop t`, RSP := RSP + 8. -/
def retState (t : RamState) : RamState :=
  (Operand.reg 4 : Operand 64).write
    { dataAccess t "load" with RIP := stackTop t, Branch_Taken := true } (stackPtr t + 8)

theorem setSliceChecked_full_run {σ : Type} (t : X86.State σ) (x v : BitVec 64) :
    (X86.Runtime.setSliceChecked x 0 64 v :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec 64)).run t = (.ok v, t) := by
  simp only [x86_runtime, setSlice_full]
  rfl

theorem zeroExtend16_zero_run {σ : Type} (t : X86.State σ) :
    (Std.Bits.Zero_Extend (source_size := 16) (0 : BitVec 16) 64 :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec 64)).run t = (.ok 0, t) := by
  simp [x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.pure]

/-- `Operations.RET_NEAR 64 64 0`: pop the 8 bytes at RSP into RIP, RSP := RSP + 8. Needs them
readable and their value below 4 GiB. -/
theorem ret_operation [Bindings] (t : RamState) (h : DataReady t) (hss : t.SS = userStackSegment)
    (hr : MemReadable t (stackPtr t) 8)
    (htarget : (stackTop t).toNat < 2^32) :
    (X86.Instructions.Operations.RET_NEAR 64 64 0).run t = (.ok (), retState t) := by
  have hb : BranchReady (dataAccess t "load") :=
    h.branchReady.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
  unfold X86.Instructions.Operations.RET_NEAR
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (get_run t)
  spec_bind_with (rsp_run t)
  spec_bind_with (popStack_run t h hss (stackPtr t) hr)
  spec_bind_with (setSliceChecked_full_run _ 0 _)
  spec_bind_with (get_run _)
  spec_bind_with (isShadowStackEnabled_run (dataAccess t "load") h.cpl h.cr4)
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (get_run _)
  spec_bind_with (checkNewRIP_run _ _ hb htarget)
  spec_bind_with (branchNear_run _ _)
  spec_bind_rfl
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (zeroExtend16_zero_run _)
  spec_bind_with (rsp_run _)
  spec_bind_with (setSliceChecked_full_run _ _ _)
  refine (rspWrite_run _ _).trans ?_
  have e : stackPtr t + 8 + (0 : BitVec 64) = stackPtr t + 8 := BitVec.add_zero _
  rw [e]
  rfl

/-- The state after a near return with an immediate from `t` (`RET imm16`): RIP := `stackTop t`,
RSP := RSP + 8 + `imm` (zero-extended). -/
def retImmState (t : RamState) (imm : BitVec 16) : RamState :=
  (Operand.reg 4 : Operand 64).write
    { dataAccess t "load" with RIP := stackTop t, Branch_Taken := true }
    (stackPtr t + 8 + imm.setWidth 64)

/-- `Operations.RET_NEAR 64 64 imm` (`C2 iw`): pop the 8 bytes at RSP into RIP, then RSP :=
RSP + 8 + `imm`. Needs them readable and their value below 4 GiB. -/
theorem ret_imm_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 8)
    (htarget : (stackTop t).toNat < 2^32) (imm : BitVec 16) :
    (X86.Instructions.Operations.RET_NEAR 64 64 imm).run t = (.ok (), retImmState t imm) := by
  have hb : BranchReady (dataAccess t "load") :=
    h.branchReady.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
  have hz : ∀ u : RamState, (Std.Bits.Zero_Extend (source_size := 16) imm 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run u = (.ok (imm.setWidth 64), u) :=
    fun u => by simp [x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.pure]
  unfold X86.Instructions.Operations.RET_NEAR
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_rfl
  spec_bind_with (get_run t)
  spec_bind_with (rsp_run t)
  spec_bind_with (popStack_run t h hss (stackPtr t) hr)
  spec_bind_with (setSliceChecked_full_run _ 0 _)
  spec_bind_with (get_run _)
  spec_bind_with (isShadowStackEnabled_run (dataAccess t "load") h.cpl h.cr4)
  simp only [Bool.false_eq_true, ↓reduceIte]
  spec_bind_with (get_run _)
  spec_bind_with (checkNewRIP_run _ _ hb htarget)
  spec_bind_with (branchNear_run _ _)
  spec_bind_rfl
  spec_bind_with (checkedSliceRead_full_run _ _)
  spec_bind_with (hz _)
  spec_bind_with (rsp_run _)
  spec_bind_with (setSliceChecked_full_run _ _ _)
  exact (rspWrite_run _ _).trans rfl

/-- Layer 2 for `CALL_NEAR_RELBRd` (`E8 rel32`): `ip` is the address of the displacement. If
fetching it returns `disp` and leaves `v`, the form pushes `ip + 4` and branches to
`ip + 4 + sext disp`. -/
theorem call_rel32_form [Bindings] (u v : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (disp : BitVec 32) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 32).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (h : DataReady v) (hss : v.SS = userStackSegment)
    (htarget : (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64)).toNat < 2^32)
    (hw : MemWritable v (pushAddr v) 8) :
    (X86.Instructions.CALL_NEAR_RELBRd ip ctx).run u =
      (.ok (), callState (withNextIP v (BitVec.add ip 4#64)) (BitVec.add ip 4#64)
        (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64))) := by
  unfold X86.Instructions.CALL_NEAR_RELBRd
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 4)) _ (s := v)
    (value := BitVec.add ip 4#64) rfl).trans ?_
  refine (specM_bind_run _ _ (s := v) (t := withNextIP v (BitVec.add ip 4#64)) (value := ()) rfl).trans ?_
  exact call_operation_rel _ ctx _ (h.withNextIP _) hss (hmode.of_cs_lma_eq rfl rfl) htarget
    (hw.of_external_eq rfl)

/-- Layer 2 for `CALL_NEAR_GPRv` (`FF /2`, `mod = 3`): in 64-bit mode (operand size 64 whatever
the prefixes) without LOCK, push `ip` and branch to register `rm` (extended by REX.B). -/
theorem call_r_form [Bindings] (t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hmode64 : ctx.is_mode64 = true)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment)
    (htarget : ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 64).read t).toNat <
      2^32)
    (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.CALL_NEAR_GPRv ip ctx rm).run t =
      (.ok (), callState (withNextIP t ip) ip
        ((Operand.reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm) : Operand 64).read t)) := by
  have hcontext : ({ ctx with is_mode64 := true, lock_prefix_present := false } :
      Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  simp only [Operand.read_reg64] at htarget ⊢
  unfold X86.Instructions.CALL_NEAR_GPRv
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    X86.Instructions.Operations.CALL_NEAR => call_operation_abs (withNextIP t ip) _ _ _
      (h.withNextIP ip) hss htarget (hw.of_external_eq rfl)]

/-- Layer 2 for `CALL_NEAR_MEMv` (`FF /2`, `mod ≠ 3`) through any segment: if the address
computation returns `off` in segment `seg` and leaves `t`, RIP-relative handling gives `addr`, and
`addr`'s linear address in `seg` is `lin` (`SegAccess`: `addr` itself for a flat segment, the base
plus `addr` for FS or GS), at any address size `asz` (64, or 32 after `67`), the form reads the 8 bytes at `lin` (`dataAccess t "load"`), sets
`Next_IP := next`, pushes `next` (on SS, which takes no override) and branches to the value read. -/
theorem call_m_seg_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hmode64 : ctx.is_mode64 = true) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hread : MemReadable t lin 8)
    (htarget : ((Operand.mem lin : Operand 64).read t).toNat < 2^32)
    (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.CALL_NEAR_MEMv ip ctx mod rm).run s =
      (.ok (), callState (withNextIP (dataAccess t "load") next) next
        ((Operand.mem lin : Operand 64).read t)) := by
  have hcontext :
      ({ ctx with is_mode64 := true, address_size := asz, lock_prefix_present := false } :
        Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext] at hea
  rw [← hcontext]
  have hread' := logicalMemRead_run_seg t h seg addr lin hseg 64 (by decide) .Memory_Read
    (.inl rfl) hread.low hread.mem
  have hd : DataReady (withNextIP (dataAccess t "load") next) :=
    h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables
  unfold X86.Instructions.CALL_NEAR_MEMv
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Read => hread',
    X86.Instructions.Operations.CALL_NEAR => call_operation_abs _ _ _ _ hd hss htarget
      (hw.of_external_eq rfl)]

/-- Layer 2 for `CALL_NEAR_MEMv` (`FF /2`, `mod ≠ 3`): if the address computation returns `off`
in a flat data segment and leaves `t`, and RIP-relative handling gives `addr`, the form reads the
8 bytes at `addr` (`dataAccess t "load"`), sets `Next_IP := next`, pushes `next` and branches to the
value read (`call_m_seg_form` with `SegAccess.flat`). -/
theorem call_m_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hmode64 : ctx.is_mode64 = true) (haddr : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hread : MemReadable t addr 8)
    (htarget : ((Operand.mem addr : Operand 64).read t).toNat < 2^32)
    (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.CALL_NEAR_MEMv ip ctx mod rm).run s =
      (.ok (), callState (withNextIP (dataAccess t "load") next) next
        ((Operand.mem addr : Operand 64).read t)) :=
  call_m_seg_form s t ip ctx mod rm hmode64 haddr hlock off next addr _ isRip hea hrip addr
    (SegAccess.flat isStack addr) h hss hread htarget hw

/-- Layer 2 for `RET_NEAR` (`C3`): in 64-bit mode without LOCK, `Next_IP := ip`, then
`ret_operation`. -/
theorem ret_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hmode64 : ctx.is_mode64 = true) (hlock : ctx.lock_prefix_present = false)
    (hmode : In64BitMode t) (h : DataReady t) (hss : t.SS = userStackSegment)
    (hr : MemReadable t (stackPtr t) 8) (htarget : (stackTop t).toNat < 2^32) :
    (X86.Instructions.RET_NEAR ip ctx).run t = (.ok (), retState (withNextIP t ip)) := by
  have hcontext : ({ ctx with is_mode64 := true, lock_prefix_present := false } :
      Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hsas : (Stack_Address_Size t.SS).run t = (.ok 64, t) := by
    rw [hss]; exact stackAddressSize_run t hmode
  unfold X86.Instructions.RET_NEAR
  spec_run [MonadState.get => get_run _, Stack_Address_Size => hsas,
    X86.Instructions.Operations.RET_NEAR => ret_operation (withNextIP t ip) (h.withNextIP ip) hss
      (hr.of_external_eq rfl) htarget]

end X86Proofs
