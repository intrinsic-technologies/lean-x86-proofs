import X86Proofs.Instructions.Call.Form
import X86Proofs.Instructions.Movs.RepForm

/-!
# LOOP, LOOPE, LOOPNE specification

`LOOP rel8` (`E2`), `LOOPE rel8` (`E1`) and `LOOPNE rel8` (`E0`) with address size 64: the count
RCX - 1 is written back to RCX, and the branch to `Next_IP + sext rel8` is taken if the count is not
zero, and for LOOPE also ZF is set, for LOOPNE ZF is clear (the SDM's `IF Count ≠ 0 [AND ZF = 1 /
ZF = 0]`). No flag is written. `loopTaken kind count zf` is that condition, `loopState t taken
target` the state after the instruction's operation from `t` (with `Next_IP` already set): RIP :=
`target` and `Branch_Taken` if taken, and RCX := RCX - 1. With a `67` prefix (address size 32)
the count is ECX - 1 (`loopCount32`, written back zero-extended: `loop32State`).

lean-x86 raises #UD for LOOPE and LOOPNE when the processor configuration `MODEP5` is set
(`configModeP5_run` reads it as clear, given that).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- Whether `LOOP` (`kind`) branches, for the decremented count `count` and the flag ZF `zf`. -/
def loopTaken (kind : Instruction_Loop_Type) (count : BitVec 64) (zf : Bool) : Bool :=
  match kind with
  | .LOOP => !(count == 0)
  | .LOOPE => !(count == 0) && zf
  | .LOOPNE => !(count == 0) && !zf

/-- The state after a `LOOP` operation from `t`: a near branch to `target` if `taken`, and
RCX := RCX - 1. -/
def loopState (t : RamState) (taken : Bool) (target : BitVec 64) : RamState :=
  rcx.write (if taken then { t with RIP := target, Branch_Taken := true } else t) (rcx.read t - 1)

/-- The count of `LOOP` at address size 32 (a `67` prefix): ECX - 1, zero-extended (RCX's new
value). `loopTaken` of it is the SDM's `Count ≠ 0` test on ECX. -/
def loopCount32 (t : RamState) : BitVec 64 := ((rcx.read t).setWidth 32 - 1).setWidth 64

attribute [x86_pre_simp] loopCount32

/-- `loopState` at address size 32: a near branch to `target` if `taken`, and RCX :=
`loopCount32 t`. -/
def loop32State (t : RamState) (taken : Bool) (target : BitVec 64) : RamState :=
  rcx.write (if taken then { t with RIP := target, Branch_Taken := true } else t) (loopCount32 t)

theorem configModeP5_run [Bindings] (s : RamState)
    (hp5 : Bindings.processor.config.MODEP5 = false) :
    (liftM (Config.Read.MODEP5 (exception := X86.Exception)) :
      X86.Runtime.SpecM X86.Exception RamState Bool).run s = (.ok false, s) := by
  show (Config.Read.MODEP5, s) = _
  unfold Config.Read.MODEP5
  rw [show (Config.Value.MODEP5.value : Bool) = false from hp5]
  rfl

theorem loop_operation [Bindings] (t : RamState) (kind : Instruction_Loop_Type)
    (ctx : Instruction_Context) (disp : BitVec 8) (hmode : In64BitMode t) (hready : BranchReady t)
    (htarget : loopTaken kind (rcx.read t - 1) (StatusFlags.ofRFLAGS t.RFLAGS).ZF = true →
      (BitVec.add t.Next_IP (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.Operations.LOOP kind 64 8 ctx disp).run t =
      (.ok (), loopState t (loopTaken kind (rcx.read t - 1) (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
        (BitVec.add t.Next_IP (disp.signExtend 64))) := by
  have hsub : (liftM (Std.Bits.Subtract_int (n := 64) (rcx.read t) 1) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run t = (.ok (rcx.read t - 1), t) :=
    rfl
  have hzero (v : BitVec 64) : (liftM (Std.Bits.Is_Zero (size := 64) v) :
      X86.Runtime.SpecM X86.Exception RamState Bool).run t = (.ok (v == 0#64), t) := rfl
  have hzf : (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run t =
      (.ok (t.RFLAGS.extractLsb' 6 1), t) := rfl
  unfold X86.Instructions.Operations.LOOP
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := t) (t := t) (value := rcx.read t)
    ((specM_bind_run _ _ rfl).trans ((specM_bind_run _ _ (rcx_run t)).trans
      (checkedSliceRead_full_run t _)))).trans ?_
  refine (specM_bind_run _ _ hsub).trans ?_
  have hE : strictAnd (!(rcx.read t - 1 == 0#64)) (t.RFLAGS.extractLsb' 6 1 == 1) =
      loopTaken .LOOPE (rcx.read t - 1) (StatusFlags.ofRFLAGS t.RFLAGS).ZF := by
    rw [extractLsb'_one_eq_ofBool]
    simp only [StatusFlags.ofRFLAGS, loopTaken, strictAnd]
    cases t.RFLAGS.getLsbD 6 <;> cases (rcx.read t - 1 == 0#64) <;> rfl
  have hNE : strictAnd (!(rcx.read t - 1 == 0#64)) (t.RFLAGS.extractLsb' 6 1 == 0) =
      loopTaken .LOOPNE (rcx.read t - 1) (StatusFlags.ofRFLAGS t.RFLAGS).ZF := by
    rw [extractLsb'_one_eq_ofBool]
    simp only [StatusFlags.ofRFLAGS, loopTaken, strictAnd]
    cases t.RFLAGS.getLsbD 6 <;> cases (rcx.read t - 1 == 0#64) <;> rfl
  cases kind
  case' LOOP =>
    refine (specM_bind_run _ _ (hzero _)).trans ?_
    refine (specM_bind_run _ _ (s := t)
      (value := loopTaken .LOOP (rcx.read t - 1) (StatusFlags.ofRFLAGS t.RFLAGS).ZF) rfl).trans ?_
  case' LOOPE =>
    refine (specM_bind_run _ _ (hzero _)).trans ?_
    refine (specM_bind_run _ _ hzf).trans ?_
    refine (specM_bind_run _ _ (s := t)
      (value := loopTaken .LOOPE (rcx.read t - 1) (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
      (by rw [← hE]; rfl)).trans ?_
  case' LOOPNE =>
    refine (specM_bind_run _ _ (hzero _)).trans ?_
    refine (specM_bind_run _ _ hzf).trans ?_
    refine (specM_bind_run _ _ (s := t)
      (value := loopTaken .LOOPNE (rcx.read t - 1) (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
      (by rw [← hNE]; rfl)).trans ?_
  all_goals
    generalize loopTaken _ _ _ = b at htarget ⊢
    cases b
    · dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (writeRCX64_run t _).trans rfl
    · dsimp only
      simp only [↓reduceIte]
      spec_bind_with (get_run t)
      refine (specM_bind_run _ _ (s := t) (value := disp.signExtend 64) rfl).trans ?_
      spec_bind_with (relativeBranchWrap_run t _ _ hmode)
      spec_bind_with (get_run t)
      spec_bind_with (checkNewRIP_run t _ hready (htarget rfl))
      spec_bind_with (branchNear_run t _)
      exact (writeRCX64_run _ _).trans rfl

theorem loop32_operation [Bindings] (t : RamState) (kind : Instruction_Loop_Type)
    (ctx : Instruction_Context) (disp : BitVec 8) (hmode : In64BitMode t) (hready : BranchReady t)
    (htarget : loopTaken kind (loopCount32 t) (StatusFlags.ofRFLAGS t.RFLAGS).ZF = true →
      (BitVec.add t.Next_IP (disp.signExtend 64)).toNat < 2^32) :
    (X86.Instructions.Operations.LOOP kind 32 8 ctx disp).run t =
      (.ok (), loop32State t (loopTaken kind (loopCount32 t) (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
        (BitVec.add t.Next_IP (disp.signExtend 64))) := by
  have hslice : (X86.Runtime.CheckedSlice.read (rcx.read t) 0 32 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run t =
        (.ok ((rcx.read t).setWidth 32), t) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk,
      StateT.pure, BitVec.setWidth_eq_extractLsb']
  have hsub : (liftM (Std.Bits.Subtract_int (n := 32) ((rcx.read t).setWidth 32) 1) :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 32)).run t =
        (.ok ((rcx.read t).setWidth 32 - 1), t) := rfl
  have hzero (v : BitVec 32) : (liftM (Std.Bits.Is_Zero (size := 32) v) :
      X86.Runtime.SpecM X86.Exception RamState Bool).run t = (.ok (v == 0#32), t) := rfl
  have hz (v : BitVec 32) : (v.setWidth 64 == (0 : BitVec 64)) = (v == 0#32) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := v.isLt
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at h1
      simpa using h1
    · rintro rfl
      rfl
  have hzf : (RFLAGS.ZF : X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run t =
      (.ok (t.RFLAGS.extractLsb' 6 1), t) := rfl
  unfold X86.Instructions.Operations.LOOP
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (s := t) (t := t) (value := (rcx.read t).setWidth 32)
    ((specM_bind_run _ _ rfl).trans ((specM_bind_run _ _ (rcx_run t)).trans hslice))).trans ?_
  refine (specM_bind_run _ _ hsub).trans ?_
  have hL : (!((rcx.read t).setWidth 32 - 1 == 0#32)) =
      loopTaken .LOOP (loopCount32 t) (StatusFlags.ofRFLAGS t.RFLAGS).ZF := by
    simp only [loopTaken, loopCount32, hz]
  have hE : strictAnd (!((rcx.read t).setWidth 32 - 1 == 0#32)) (t.RFLAGS.extractLsb' 6 1 == 1) =
      loopTaken .LOOPE (loopCount32 t) (StatusFlags.ofRFLAGS t.RFLAGS).ZF := by
    rw [extractLsb'_one_eq_ofBool]
    simp only [StatusFlags.ofRFLAGS, loopTaken, loopCount32, hz, strictAnd]
    cases t.RFLAGS.getLsbD 6 <;> cases ((rcx.read t).setWidth 32 - 1 == 0#32) <;> rfl
  have hNE : strictAnd (!((rcx.read t).setWidth 32 - 1 == 0#32)) (t.RFLAGS.extractLsb' 6 1 == 0) =
      loopTaken .LOOPNE (loopCount32 t) (StatusFlags.ofRFLAGS t.RFLAGS).ZF := by
    rw [extractLsb'_one_eq_ofBool]
    simp only [StatusFlags.ofRFLAGS, loopTaken, loopCount32, hz, strictAnd]
    cases t.RFLAGS.getLsbD 6 <;> cases ((rcx.read t).setWidth 32 - 1 == 0#32) <;> rfl
  cases kind
  case' LOOP =>
    refine (specM_bind_run _ _ (hzero _)).trans ?_
    refine (specM_bind_run _ _ (s := t)
      (value := loopTaken .LOOP (loopCount32 t) (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
      (by rw [← hL]; rfl)).trans ?_
  case' LOOPE =>
    refine (specM_bind_run _ _ (hzero _)).trans ?_
    refine (specM_bind_run _ _ hzf).trans ?_
    refine (specM_bind_run _ _ (s := t)
      (value := loopTaken .LOOPE (loopCount32 t) (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
      (by rw [← hE]; rfl)).trans ?_
  case' LOOPNE =>
    refine (specM_bind_run _ _ (hzero _)).trans ?_
    refine (specM_bind_run _ _ hzf).trans ?_
    refine (specM_bind_run _ _ (s := t)
      (value := loopTaken .LOOPNE (loopCount32 t) (StatusFlags.ofRFLAGS t.RFLAGS).ZF)
      (by rw [← hNE]; rfl)).trans ?_
  all_goals
    generalize loopTaken _ _ _ = b at htarget ⊢
    cases b
    · dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (writeRCX32_run t _).trans rfl
    · dsimp only
      simp only [↓reduceIte]
      spec_bind_with (get_run t)
      refine (specM_bind_run _ _ (s := t) (value := disp.signExtend 64) rfl).trans ?_
      spec_bind_with (relativeBranchWrap_run t _ _ hmode)
      spec_bind_with (get_run t)
      spec_bind_with (checkNewRIP_run t _ hready (htarget rfl))
      spec_bind_with (branchNear_run t _)
      exact (writeRCX32_run _ _).trans rfl

theorem signExtend_8_32_64 (d : BitVec 8) : (d.signExtend 32).signExtend 64 = d.signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.msb_signExtend]
  by_cases h8 : i < 8 <;> by_cases h32 : i < 32 <;> simp [h8, h32, hi] <;> omega

theorem signExtend_8_32_64_run {σ : Type} (d : BitVec 8) (t : X86.State σ) :
    (Std.Bits.Sign_Extend (source_size := 32) (BitVec.ofInt (Int.toNat 32) d.toInt) 64 :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec 64)).run t =
        (.ok (d.signExtend 64), t) := by
  rw [← signExtend_8_32_64]
  simp [x86_runtime, pure, ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.pure]
  rfl

end X86Proofs
