import X86Proofs.Instructions.Branch.Cond
import X86Proofs.Instructions.Nop.Form
import X86Proofs.Step.Fetch

/-!
# Layer 2: relative branch forms

The near relative branches fetch a displacement, set `Next_IP` past it and, if they branch, set
RIP to `Next_IP` + the sign-extended displacement and `Branch_Taken` (so the step does not
overwrite RIP with `Next_IP`). Their result on the state `v` after the displacement fetch is
`branchState v taken nextIP target`: `jumpState v nextIP target` if taken, else `withNextIP v
nextIP` (as for a NOP).

- `jcc_rel8_form` / `jcc_rel32_form`: `JO_RELBRb_0` (`70+cc rel8`) and `JO_RELBRd_0`
  (`0F 80+cc rel32`) with any opcode; taken iff `condHolds cc` of the flags (`cc` the opcode's low
  four bits). lean-x86 has one copy of each per condition (`JZ_RELBRb_0`, …), equal to the `JO`
  one by `rfl` (the opcode decoders, `Decode_Legacy_0_Opcode_74` etc., are too), so the lemmas are
  stated once, for the `JO` copies.
- `jmp_rel8_form` / `jmp_rel32_form`: `JMP_RELBRb_1` (`EB rel8`) and `JMP_RELBRd` (`E9 rel32`),
  always taken.
- `jmp_operation_abs`: `JMP_NEAR` with an absolute target (`FF /4`, register or memory), for the
  generated `Instructions/Jmp`.

A taken branch checks that the target is canonical (`Check_New_RIP`); `checkNewRIP_run` passes
it for a target below 4 GiB in the flat 64-bit code segment. `JMP_NEAR` also asks whether CET
end-branch tracking is on (`isEndBranchEnabledAndNotSuppressed_run`: not with `CR4.CET` clear).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- `s` after a taken near branch to `target` past an instruction ending at `nextIP`. -/
def jumpState {σ : Type} (s : X86.State σ) (nextIP target : BitVec 64) : X86.State σ :=
  { s with Next_IP := nextIP, RIP := target, Branch_Taken := true }

/-- `s` after a near branch to `target`, taken or not, past an instruction ending at `nextIP`. -/
def branchState {σ : Type} (s : X86.State σ) (taken : Bool) (nextIP target : BitVec 64) :
    X86.State σ :=
  if taken then jumpState s nextIP target else withNextIP s nextIP

@[simp] theorem branchState_CS {σ : Type} (s : X86.State σ) (taken : Bool)
    (nextIP target : BitVec 64) : (branchState s taken nextIP target).CS = s.CS := by
  cases taken <;> rfl

@[simp] theorem branchState_IA32_EFER {σ : Type} (s : X86.State σ) (taken : Bool)
    (nextIP target : BitVec 64) :
    (branchState s taken nextIP target).IA32_EFER = s.IA32_EFER := by
  cases taken <;> rfl

/-- The machine facts a taken branch's checks need, on the state the form runs in: the flat
64-bit code segment, paging controls, no LAM, and no CET. -/
structure BranchReady [Bindings] (t : RamState) : Prop where
  cs : t.CS = userCodeSegment
  lma : t.IA32_EFER.LMA = 1
  cpl : 0 ≤ t.CPL ∧ t.CPL ≤ 3
  cr0 : Prelude.SupportedIntegerCR0 t.CR0
  cr4 : Prelude.SupportedIntegerCR4 t.CR4
  lme : t.IA32_EFER.LME = 1
  lam : Prelude.ReportsCPUFeature Bindings.processor t CPUID_LAM_Encoding false

/-- `Check_New_RIP` passes for a target below 4 GiB in the flat 64-bit code segment. -/
theorem checkNewRIP_run [Bindings] (t : RamState) (target : BitVec 64) (h : BranchReady t)
    (htarget : target.toNat < 2^32) :
    (Check_New_RIP t.CS target).run t = (.ok (), t) := by
  unfold Check_New_RIP
  rw [h.cs]
  refine (specM_bind_run _ _ (is64BitCodeSegment_userCodeSegment_run t h.lma)).trans ?_
  have hcan := isCanonicalWrtPagingMode_run t target 0 h.cr0 h.cr4 h.lme h.lam htarget (by omega)
    true
  rw [show ((0 : Nat) : Int) * 8 = 0 from rfl] at hcan
  refine (specM_bind_run _ _ hcan).trans ?_
  rfl

/-- In 64-bit mode `Relative_Branch_Wrap` keeps the full 64-bit target. -/
theorem relativeBranchWrap_run {σ : Type} (t : X86.State σ) (size : Int) (target : BitVec 64)
    (hmode : In64BitMode t) : (Relative_Branch_Wrap size target).run t = (.ok target, t) := by
  unfold Relative_Branch_Wrap
  refine (specM_bind_run _ _ hmode).trans ?_
  simp only [HOr.hOr, OrOp.or, strictOr, Bool.true_or, ↓reduceIte]
  rfl

/-- With `CR4.CET` clear, CET end-branch tracking is off. -/
theorem isEndBranchEnabledAndNotSuppressed_run {σ : Type} (s : X86.State σ) (hcpl : 0 ≤ s.CPL ∧ s.CPL ≤ 3)
    (hcr4 : Prelude.SupportedIntegerCR4 s.CR4) :
    (Is_End_Branch_Enabled_And_Not_Suppressed s.CPL).run s = (.ok false, s) := by
  simp [Is_End_Branch_Enabled_And_Not_Suppressed, cr4CET_eq, cr0PE_eq, rflagsVM_eq,
    x86_runtime, hcpl, HAnd.hAnd, AndOp.and, strictAnd, supportedIntegerCR4_extractLsb_cet hcr4,
    bind, pure, get, getThe, ExceptT.bind, ExceptT.pure, ExceptT.run, ExceptT.mk, ExceptT.bindCont,
    StateT.bind, StateT.pure, MonadStateOf.get, StateT.get, Functor.map, StateT.map, Bind.bind,
    Pure.pure, ExceptT.lift, liftM, monadLift, MonadLift.monadLift]

/-- Sign-extending a 64-bit value to 64 bits changes nothing. -/
theorem signExtend64_run {σ : Type} (x : BitVec 64) (t : X86.State σ) :
    (Std.Bits.Sign_Extend (source_size := 64) x 64 :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec 64)).run t = (.ok x, t) := by
  simp [x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.pure]

/--
lean-x86's `Operations.Jcc` at 64 bits, from a state `t` with `Next_IP` set: if `condHolds cc`
of the flags, a near branch to `Next_IP + off`, else nothing.
-/
theorem jcc_operation [Bindings] (t : RamState) (ctx : Instruction_Context) (cc : BitVec 4)
    (off : BitVec 64) (hmode : In64BitMode t)
    (hcheck : condHolds cc (StatusFlags.ofRFLAGS t.RFLAGS) = true →
      (Check_New_RIP t.CS (BitVec.add t.Next_IP off)).run t = (.ok (), t)) :
    (X86.Instructions.Operations.Jcc 64 ctx cc off).run t =
      (.ok (), if condHolds cc (StatusFlags.ofRFLAGS t.RFLAGS) then
        { t with RIP := BitVec.add t.Next_IP off, Branch_Taken := true } else t) := by
  unfold X86.Instructions.Operations.Jcc
  refine (specM_bind_run _ _ (s := t) (t := t) (value := ()) rfl).trans ?_
  refine (specM_bind_run _ _ (conditionHolds_run t cc)).trans ?_
  cases hc : condHolds cc (StatusFlags.ofRFLAGS t.RFLAGS)
  · rfl
  · simp only [↓reduceIte]
    refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _
      (s := t) rfl).trans ?_
    refine (specM_bind_run _ _ (signExtend64_run off t)).trans ?_
    refine (specM_bind_run _ _ (relativeBranchWrap_run t _ _ hmode)).trans ?_
    refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _
      (s := t) rfl).trans ?_
    refine (specM_bind_run _ _ (hcheck hc)).trans ?_
    rfl

/-- The branch facts carry over to a state with the same controls, code segment, EFER and
CPL. -/
theorem BranchReady.of_eq [Bindings] {s t : RamState} (h : BranchReady s) (hst : SameControls s t)
    (hcs : t.CS = s.CS) (hefer : t.IA32_EFER = s.IA32_EFER) (hcpl : t.CPL = s.CPL) :
    BranchReady t :=
  ⟨hcs.trans h.cs, hefer ▸ h.lma, hcpl ▸ h.cpl, hst.cr0 ▸ h.cr0, hst.cr4 ▸ h.cr4, hefer ▸ h.lme,
    reportsCPUFeature_of_sameControls hst h.lam⟩

theorem BranchReady.withNextIP [Bindings] {s : RamState} (h : BranchReady s) (n : BitVec 64) :
    BranchReady (withNextIP s n) :=
  h.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

theorem BranchReady.jumpState [Bindings] {s : RamState} (h : BranchReady s) (n t : BitVec 64) :
    BranchReady (jumpState s n t) :=
  h.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

/-- The `Jcc` forms after the displacement fetch: set `Next_IP`, then `Operations.Jcc`. -/
theorem jcc_tail [Bindings] (v : RamState) (ctx : Instruction_Context) (cc : BitVec 4)
    (nextIP off : BitVec 64) (hmode : In64BitMode v) (hready : BranchReady v)
    (htarget : condHolds cc (StatusFlags.ofRFLAGS v.RFLAGS) = true →
      (BitVec.add nextIP off).toNat < 2^32) :
    (do Next_IP.assign nextIP; X86.Instructions.Operations.Jcc 64 ctx cc off :
      X86.Runtime.SpecM X86.Exception RamState Unit).run v =
      (.ok (), branchState v (condHolds cc (StatusFlags.ofRFLAGS v.RFLAGS)) nextIP
        (BitVec.add nextIP off)) := by
  refine (specM_bind_run _ _ (s := v) (t := withNextIP v nextIP) (value := ()) rfl).trans ?_
  refine (jcc_operation (withNextIP v nextIP) ctx cc off (hmode.of_cs_lma_eq rfl rfl)
    fun hc => checkNewRIP_run _ _ (hready.withNextIP nextIP) (htarget hc)).trans ?_
  rw [show (withNextIP v nextIP).RFLAGS = v.RFLAGS from rfl]
  unfold branchState
  cases condHolds cc (StatusFlags.ofRFLAGS v.RFLAGS) <;> rfl

/--
Layer 2 for `Jcc rel8` (`JO_RELBRb_0`, and its per-condition copies by `rfl`): `ip` is the address
of the displacement byte. If fetching it returns `disp` and leaves `v` (in 64-bit mode), the form
branches to `ip + 1 + sext disp` if `condHolds` of the opcode's low four bits holds of the flags,
else only sets `Next_IP := ip + 1`.
-/
theorem jcc_rel8_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (op disp : BitVec 8) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (hready : BranchReady v)
    (htarget : condHolds (op.extractLsb' 0 4) (StatusFlags.ofRFLAGS v.RFLAGS) = true →
      (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.JO_RELBRb_0 ip ctx op).run u =
      (.ok (), branchState v (condHolds (op.extractLsb' 0 4) (StatusFlags.ofRFLAGS v.RFLAGS))
        (BitVec.add ip 1#64) (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64))) := by
  unfold X86.Instructions.JO_RELBRb_0
  spec_bind_rfl
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := v)
    (value := BitVec.add ip 1#64) rfl).trans ?_
  exact jcc_tail v ctx (op.extractLsb' 0 4) _ (disp.signExtend 64) hmode hready htarget

/-- Layer 2 for `Jcc rel32` (`JO_RELBRd_0`, `0F 80+cc`, and its per-condition copies by `rfl`): as
`jcc_rel8_form` with a 32-bit displacement at `ip`; `Next_IP` is `ip + 4`. -/
theorem jcc_rel32_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (op : BitVec 8) (disp : BitVec 32) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 32).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (hready : BranchReady v)
    (htarget : condHolds (op.extractLsb' 0 4) (StatusFlags.ofRFLAGS v.RFLAGS) = true →
      (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.JO_RELBRd_0 ip ctx op).run u =
      (.ok (), branchState v (condHolds (op.extractLsb' 0 4) (StatusFlags.ofRFLAGS v.RFLAGS))
        (BitVec.add ip 4#64) (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64))) := by
  unfold X86.Instructions.JO_RELBRd_0
  spec_bind_rfl
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 4)) _ (s := v)
    (value := BitVec.add ip 4#64) rfl).trans ?_
  exact jcc_tail v ctx (op.extractLsb' 0 4) _ (disp.signExtend 64) hmode hready htarget

/-- `JMP_NEAR` with a relative operand, after `Next_IP` is set: a near branch to
`nextIP + off`. -/
theorem jmp_tail [Bindings] (v : RamState) (ctx : Instruction_Context) (nextIP off : BitVec 64)
    (hmode : In64BitMode v) (hready : BranchReady v)
    (htarget : (BitVec.add nextIP off).toNat < 2^32) :
    (do Next_IP.assign nextIP
        X86.Instructions.Operations.JMP_NEAR 64 ctx off false false :
      X86.Runtime.SpecM X86.Exception RamState Unit).run v =
      (.ok (), jumpState v nextIP (BitVec.add nextIP off)) := by
  refine (specM_bind_run _ _ (s := v) (t := withNextIP v nextIP) (value := ()) rfl).trans ?_
  have hw := hready.withNextIP nextIP
  have hj := hready.jumpState nextIP (BitVec.add nextIP off)
  unfold X86.Instructions.Operations.JMP_NEAR
  refine (specM_bind_run _ _ (s := withNextIP v nextIP) (value := ()) rfl).trans ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _
    (s := withNextIP v nextIP) rfl).trans ?_
  refine (specM_bind_run _ _ (signExtend64_run off _)).trans ?_
  refine (specM_bind_run _ _ (relativeBranchWrap_run (withNextIP v nextIP) _ _
    (hmode.of_cs_lma_eq rfl rfl))).trans ?_
  refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _
    (s := withNextIP v nextIP) rfl).trans ?_
  refine (specM_bind_run _ _ (checkNewRIP_run _ _ hw htarget)).trans ?_
  refine (specM_bind_run _ _ (s := withNextIP v nextIP)
    (t := jumpState v nextIP (BitVec.add nextIP off)) (value := ()) rfl).trans ?_
  refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _
    (s := jumpState v nextIP (BitVec.add nextIP off)) rfl).trans ?_
  refine (specM_bind_run _ _ (isEndBranchEnabledAndNotSuppressed_run _ hj.cpl hj.cr4)).trans ?_
  rfl

/-- `JMP_NEAR` with an absolute, indirect operand (`FF /4`: a register or memory), from `t` with
`Next_IP` set: a near branch to `target`. CET end-branch tracking is off, so the no-track prefix
does not matter. -/
theorem jmp_operation_abs [Bindings] (t : RamState) (ctx : Instruction_Context)
    (target : BitVec 64) (noTrack : Bool) (hready : BranchReady t)
    (htarget : target.toNat < 2^32) :
    (X86.Instructions.Operations.JMP_NEAR 64 ctx target true noTrack).run t =
      (.ok (), { t with RIP := target, Branch_Taken := true }) := by
  have hz : (Std.Bits.Zero_Extend (source_size := 64) target 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run t = (.ok target, t) := by
    simp [x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.pure]
  have hj : BranchReady { t with RIP := target, Branch_Taken := true } :=
    hready.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
  unfold X86.Instructions.Operations.JMP_NEAR
  refine (specM_bind_run _ _ (s := t) (value := ()) rfl).trans ?_
  simp only [↓reduceIte]
  refine (specM_bind_run _ _ hz).trans ?_
  refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _
    (s := t) rfl).trans ?_
  refine (specM_bind_run _ _ (checkNewRIP_run _ _ hready htarget)).trans ?_
  refine (specM_bind_run _ _ (s := t) (t := { t with RIP := target, Branch_Taken := true })
    (value := ()) rfl).trans ?_
  refine (specM_bind_run (get : X86.Runtime.SpecM X86.Exception RamState RamState) _
    (s := { t with RIP := target, Branch_Taken := true }) rfl).trans ?_
  refine (specM_bind_run _ _ (isEndBranchEnabledAndNotSuppressed_run _ hj.cpl hj.cr4)).trans ?_
  rfl

/-- Layer 2 for `JMP rel8` (`JMP_RELBRb_1`, `EB`): `ip` is the address of the displacement byte;
the form branches to `ip + 1 + sext disp`. -/
theorem jmp_rel8_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (disp : BitVec 8) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (hready : BranchReady v)
    (htarget : (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.JMP_RELBRb_1 ip ctx).run u =
      (.ok (), jumpState v (BitVec.add ip 1#64)
        (BitVec.add (BitVec.add ip 1#64) (disp.signExtend 64))) := by
  unfold X86.Instructions.JMP_RELBRb_1
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := v)
    (value := BitVec.add ip 1#64) rfl).trans ?_
  exact jmp_tail v ctx _ (disp.signExtend 64) hmode hready htarget

/-- Layer 2 for `JMP rel32` (`JMP_RELBRd`, `E9`): as `jmp_rel8_form` with a 32-bit displacement;
`Next_IP` is `ip + 4`. -/
theorem jmp_rel32_form [Bindings] (u v : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (disp : BitVec 32) (hlock : ctx.lock_prefix_present = false)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 32).run u = (.ok disp, v)) (hmode : In64BitMode v)
    (hready : BranchReady v)
    (htarget : (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.JMP_RELBRd ip ctx).run u =
      (.ok (), jumpState v (BitVec.add ip 4#64)
        (BitVec.add (BitVec.add ip 4#64) (disp.signExtend 64))) := by
  unfold X86.Instructions.JMP_RELBRd
  refine (specM_bind_run _ _ hfetch).trans ?_
  spec_bind_rfl
  simp only [hrex2, hlock, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 4)) _ (s := v)
    (value := BitVec.add ip 4#64) rfl).trans ?_
  exact jmp_tail v ctx _ (disp.signExtend 64) hmode hready htarget

end X86Proofs
