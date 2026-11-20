
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Cmps.Generated.Repe.Decode
import X86Proofs.Instructions.Cmps.Generated.Repe.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def repeCmpsAfter (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repeCmpsSpec n
      { t with
        Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := false }

theorem repeCmpsSpec_cs (n : Nat) (t : RamState) : (repeCmpsSpec n t).CS = t.CS := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_efer (n : Nat) (t : RamState) :
    (repeCmpsSpec n t).IA32_EFER = t.IA32_EFER := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_zmm (n : Nat) (t : RamState) : (repeCmpsSpec n t).ZMM = t.ZMM := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_mxcsr (n : Nat) (t : RamState) :
    (repeCmpsSpec n t).MXCSR = t.MXCSR := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_fp87 (n : Nat) (t : RamState) : (repeCmpsSpec n t).FP87 = t.FP87 := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_fsw (n : Nat) (t : RamState) :
    (repeCmpsSpec n t).FP87_Status = t.FP87_Status := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_ftw (n : Nat) (t : RamState) :
    (repeCmpsSpec n t).FP87_Tag_Word = t.FP87_Tag_Word := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_fcw (n : Nat) (t : RamState) :
    (repeCmpsSpec n t).FP87_Control = t.FP87_Control := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_fpuPtr (n : Nat) (t : RamState) :
    fpuPtrOf (repeCmpsSpec n t) = fpuPtrOf t := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess, fpuPtrOf]

theorem repeCmpsSpec_external (n : Nat) (t : RamState) :
    (repeCmpsSpec n t).external = t.external := by
  unfold repeCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_repeat (n : Nat) (t : RamState) :
    (repeCmpsSpec n t).Repeat_String_Operation = repeCmpsCont n t := by
  unfold repeCmpsSpec
  split <;> simp_all

theorem repeCmpsSpec_rflags (n : Nat) (t : RamState) :
    (repeCmpsSpec n t).RFLAGS = if repeCmpsCont n t then t.RFLAGS else
      (cmpSpec ((Operand.mem (rsi.read t) : Operand n).read t)
        ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := by
  unfold repeCmpsSpec
  split <;> simp_all [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_gpr (n : Nat) (t : RamState) :
    (repeCmpsSpec n t).GPR =
      Vector.set (Vector.set (Vector.set t.GPR 6 (t.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (t.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (t.GPR[1] - 1) := by
  unfold repeCmpsSpec
  split <;>
  · simp [cmpsSpec, Operand.write, Operand.read, setFlags, dataAccess, gprIndex, mergeGPR_64,
      Vector.getElem_set]
    rfl

theorem repeCmpsSpec_finish_rip (n : Nat) (t : RamState) (hb : t.Branch_Taken = false)
    (hm : t.«MSRLIST::In_Process» = false) :
    (finishStep (repeCmpsSpec n t)).RIP = if repeCmpsCont n t then t.RIP else t.Next_IP := by
  unfold finishStep repeCmpsSpec
  split <;> simp_all [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repeCmpsSpec_fixed (n : Nat) (t : RamState) :
    fixedPart (clearRep (repeCmpsSpec n t)) = fixedPart (clearRep t) := by
  unfold repeCmpsSpec
  split <;>
    simp only [fixedPart, clearRep, cmpsSpec, Operand.write, setFlags, dataAccess, beforeFetch,
      resetStepFields, clearStatusFlags_store]

theorem repeCmpsAfter_external (n len : Nat) (s : RamState) :
    (repeCmpsAfter n len s).external = s.external :=
  repeCmpsSpec_external n _

theorem repeCmpsAfter_gpr (n len : Nat) (s : RamState) :
    (repeCmpsAfter n len s).GPR =
      Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (s.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (s.GPR[1] - 1) :=
  repeCmpsSpec_gpr n _

theorem repeCmpsAfter_rsi (n len : Nat) (s : RamState) :
    rsi.read (repeCmpsAfter n len s) = rsi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repeCmpsAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repeCmpsAfter_rdi (n len : Nat) (s : RamState) :
    rdi.read (repeCmpsAfter n len s) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repeCmpsAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repeCmpsAfter_rcx (n len : Nat) (s : RamState) :
    rcx.read (repeCmpsAfter n len s) = rcx.read s - 1 := by
  simp [Operand.read, repeCmpsAfter_gpr, gprIndex]

theorem repeCmpsAfter_repeat (n len : Nat) (s : RamState) :
    (repeCmpsAfter n len s).Repeat_String_Operation = repeCmpsCont n s :=
  repeCmpsSpec_repeat n _

theorem repeCmpsAfter_rflags (n len : Nat) (s : RamState) :
    (repeCmpsAfter n len s).RFLAGS = if repeCmpsCont n s then s.RFLAGS else
      (cmpSpec ((Operand.mem (rsi.read s) : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS :=
  repeCmpsSpec_rflags n _

theorem repeCmpsAfter_rip (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repeCmpsAfter n len s).RIP =
      if repeCmpsCont n s then s.RIP else BitVec.add s.RIP (BitVec.ofNat 64 len) :=
  repeCmpsSpec_finish_rip n _ rfl hmsr

theorem AgreesExcept.repeCmps (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s)
      (clearRep (repeCmpsAfter n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repeCmpsAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6, Ne.symm h7]
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by
        rw [repeCmpsAfter, afterStep, clearRep_ZMM, finishStep_ZMM, repeCmpsSpec_zmm]
        rfl) x
    | mxcsr =>
      show _ = _
      rw [repeCmpsAfter, afterStep, clearRep_MXCSR, finishStep_MXCSR, repeCmpsSpec_mxcsr]
      rfl
    | fpr x =>
      show _ = _
      rw [repeCmpsAfter, afterStep, clearRep_FP87, finishStep_FP87, repeCmpsSpec_fp87]
      rfl
    | fsw =>
      show _ = _
      rw [repeCmpsAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repeCmpsSpec_fsw]
      rfl
    | fcc =>
      show _ = _
      rw [repeCmpsAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repeCmpsSpec_fsw]
      rfl
    | ftw =>
      show _ = _
      rw [repeCmpsAfter, afterStep, clearRep_FP87_Tag_Word, finishStep_FP87_Tag_Word,
        repeCmpsSpec_ftw]
      rfl
    | fcw =>
      show _ = _
      rw [repeCmpsAfter, afterStep, clearRep_FP87_Control, finishStep_FP87_Control,
        repeCmpsSpec_fcw]
      rfl
    | fpuPtr =>
      show _ = _
      rw [repeCmpsAfter, afterStep, fpuPtrOf_clearRep, fpuPtrOf_finishStep, repeCmpsSpec_fpuPtr]
      rfl
    | df =>
      show dfBit (repeCmpsAfter n len s).RFLAGS = dfBit s.RFLAGS
      rw [repeCmpsAfter_rflags]
      split <;> simp only [dfBit_store]
  · simp only [clearRep_external, repeCmpsAfter_external]
  · rw [repeCmpsAfter, afterStep, fixedPart_clearRep_finishStep, repeCmpsSpec_fixed]
    simp only [fixedPart, clearRep, afterFetches, beforeFetch, resetStepFields]
  · simpa [clearRep_external, repeCmpsAfter_external] using hx

theorem ReadyMidRep.repeCmps [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat) :
    ReadyMidRep (repeCmpsAfter n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repeCmpsAfter n len s)).external := by
    rw [clearRep_external, repeCmpsAfter_external]
    exact (ReadyToStep.memory (s := clearRep s) h).tables
  have : ReadyToStep (clearRep (repeCmpsAfter n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repeCmps n len s) htab
  exact this

def repeCmpsSegAfter (base : BitVec 64) (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repeCmpsSegSpec base n
      { t with
        Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := false }

theorem repeCmpsSegSpec_cs (base : BitVec 64) (n : Nat) (t : RamState) : (repeCmpsSegSpec base n t).CS = t.CS := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_efer (base : BitVec 64) (n : Nat) (t : RamState) :
    (repeCmpsSegSpec base n t).IA32_EFER = t.IA32_EFER := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_zmm (base : BitVec 64) (n : Nat) (t : RamState) : (repeCmpsSegSpec base n t).ZMM = t.ZMM := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_mxcsr (base : BitVec 64) (n : Nat) (t : RamState) :
    (repeCmpsSegSpec base n t).MXCSR = t.MXCSR := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_fp87 (base : BitVec 64) (n : Nat) (t : RamState) : (repeCmpsSegSpec base n t).FP87 = t.FP87 := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_fsw (base : BitVec 64) (n : Nat) (t : RamState) :
    (repeCmpsSegSpec base n t).FP87_Status = t.FP87_Status := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_ftw (base : BitVec 64) (n : Nat) (t : RamState) :
    (repeCmpsSegSpec base n t).FP87_Tag_Word = t.FP87_Tag_Word := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_fcw (base : BitVec 64) (n : Nat) (t : RamState) :
    (repeCmpsSegSpec base n t).FP87_Control = t.FP87_Control := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_fpuPtr (base : BitVec 64) (n : Nat) (t : RamState) :
    fpuPtrOf (repeCmpsSegSpec base n t) = fpuPtrOf t := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess, fpuPtrOf]

theorem repeCmpsSegSpec_external (base : BitVec 64) (n : Nat) (t : RamState) :
    (repeCmpsSegSpec base n t).external = t.external := by
  unfold repeCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_repeat (base : BitVec 64) (n : Nat) (t : RamState) :
    (repeCmpsSegSpec base n t).Repeat_String_Operation = repeCmpsSegCont base n t := by
  unfold repeCmpsSegSpec
  split <;> simp_all

theorem repeCmpsSegSpec_rflags (base : BitVec 64) (n : Nat) (t : RamState) :
    (repeCmpsSegSpec base n t).RFLAGS = if repeCmpsSegCont base n t then t.RFLAGS else
      (cmpSpec ((Operand.mem (base + rsi.read t) : Operand n).read t)
        ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := by
  unfold repeCmpsSegSpec
  split <;> simp_all [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_gpr (base : BitVec 64) (n : Nat) (t : RamState) :
    (repeCmpsSegSpec base n t).GPR =
      Vector.set (Vector.set (Vector.set t.GPR 6 (t.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (t.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (t.GPR[1] - 1) := by
  unfold repeCmpsSegSpec
  split <;>
  · simp [cmpsSegSpec, Operand.write, Operand.read, setFlags, dataAccess, gprIndex, mergeGPR_64,
      Vector.getElem_set]
    rfl

theorem repeCmpsSegSpec_finish_rip (base : BitVec 64) (n : Nat) (t : RamState) (hb : t.Branch_Taken = false)
    (hm : t.«MSRLIST::In_Process» = false) :
    (finishStep (repeCmpsSegSpec base n t)).RIP = if repeCmpsSegCont base n t then t.RIP else t.Next_IP := by
  unfold finishStep repeCmpsSegSpec
  split <;> simp_all [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repeCmpsSegSpec_fixed (base : BitVec 64) (n : Nat) (t : RamState) :
    fixedPart (clearRep (repeCmpsSegSpec base n t)) = fixedPart (clearRep t) := by
  unfold repeCmpsSegSpec
  split <;>
    simp only [fixedPart, clearRep, cmpsSegSpec, Operand.write, setFlags, dataAccess, beforeFetch,
      resetStepFields, clearStatusFlags_store]

theorem repeCmpsSegAfter_external (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repeCmpsSegAfter base n len s).external = s.external :=
  repeCmpsSegSpec_external base n _

theorem repeCmpsSegAfter_gpr (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repeCmpsSegAfter base n len s).GPR =
      Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (s.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (s.GPR[1] - 1) :=
  repeCmpsSegSpec_gpr base n _

theorem repeCmpsSegAfter_rsi (base : BitVec 64) (n len : Nat) (s : RamState) :
    rsi.read (repeCmpsSegAfter base n len s) = rsi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repeCmpsSegAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repeCmpsSegAfter_rdi (base : BitVec 64) (n len : Nat) (s : RamState) :
    rdi.read (repeCmpsSegAfter base n len s) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repeCmpsSegAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repeCmpsSegAfter_rcx (base : BitVec 64) (n len : Nat) (s : RamState) :
    rcx.read (repeCmpsSegAfter base n len s) = rcx.read s - 1 := by
  simp [Operand.read, repeCmpsSegAfter_gpr, gprIndex]

theorem repeCmpsSegAfter_repeat (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repeCmpsSegAfter base n len s).Repeat_String_Operation = repeCmpsSegCont base n s :=
  repeCmpsSegSpec_repeat base n _

theorem repeCmpsSegAfter_rflags (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repeCmpsSegAfter base n len s).RFLAGS = if repeCmpsSegCont base n s then s.RFLAGS else
      (cmpSpec ((Operand.mem (base + rsi.read s) : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS :=
  repeCmpsSegSpec_rflags base n _

theorem repeCmpsSegAfter_rip (base : BitVec 64) (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repeCmpsSegAfter base n len s).RIP =
      if repeCmpsSegCont base n s then s.RIP else BitVec.add s.RIP (BitVec.ofNat 64 len) :=
  repeCmpsSegSpec_finish_rip base n _ rfl hmsr

theorem AgreesExcept.repeCmpsSeg (base : BitVec 64) (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s)
      (clearRep (repeCmpsSegAfter base n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repeCmpsSegAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6, Ne.symm h7]
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by
        rw [repeCmpsSegAfter, afterStep, clearRep_ZMM, finishStep_ZMM, repeCmpsSegSpec_zmm]
        rfl) x
    | mxcsr =>
      show _ = _
      rw [repeCmpsSegAfter, afterStep, clearRep_MXCSR, finishStep_MXCSR, repeCmpsSegSpec_mxcsr]
      rfl
    | fpr x =>
      show _ = _
      rw [repeCmpsSegAfter, afterStep, clearRep_FP87, finishStep_FP87, repeCmpsSegSpec_fp87]
      rfl
    | fsw =>
      show _ = _
      rw [repeCmpsSegAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repeCmpsSegSpec_fsw]
      rfl
    | fcc =>
      show _ = _
      rw [repeCmpsSegAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repeCmpsSegSpec_fsw]
      rfl
    | ftw =>
      show _ = _
      rw [repeCmpsSegAfter, afterStep, clearRep_FP87_Tag_Word, finishStep_FP87_Tag_Word,
        repeCmpsSegSpec_ftw]
      rfl
    | fcw =>
      show _ = _
      rw [repeCmpsSegAfter, afterStep, clearRep_FP87_Control, finishStep_FP87_Control,
        repeCmpsSegSpec_fcw]
      rfl
    | fpuPtr =>
      show _ = _
      rw [repeCmpsSegAfter, afterStep, fpuPtrOf_clearRep, fpuPtrOf_finishStep, repeCmpsSegSpec_fpuPtr]
      rfl
    | df =>
      show dfBit (repeCmpsSegAfter base n len s).RFLAGS = dfBit s.RFLAGS
      rw [repeCmpsSegAfter_rflags]
      split <;> simp only [dfBit_store]
  · simp only [clearRep_external, repeCmpsSegAfter_external]
  · rw [repeCmpsSegAfter, afterStep, fixedPart_clearRep_finishStep, repeCmpsSegSpec_fixed]
    simp only [fixedPart, clearRep, afterFetches, beforeFetch, resetStepFields]
  · simpa [clearRep_external, repeCmpsSegAfter_external] using hx

theorem ReadyMidRep.repeCmpsSeg [Bindings] {s : RamState} (h : ReadyMidRep s) (base : BitVec 64) (n len : Nat) :
    ReadyMidRep (repeCmpsSegAfter base n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repeCmpsSegAfter base n len s)).external := by
    rw [clearRep_external, repeCmpsSegAfter_external]
    exact (ReadyToStep.memory (s := clearRep s) h).tables
  have : ReadyToStep (clearRep (repeCmpsSegAfter base n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repeCmpsSeg base n len s) htab
  exact this

theorem repeCmpsSegAfter_segReady (base : BitVec 64) (n len : Nat) (s : RamState) {r : SegReg} {b : BitVec 64}
    (h : r.Ready b s) : r.Ready b (repeCmpsSegAfter base n len s) := by
  have hfs : (repeCmpsSegAfter base n len s).FS = s.FS := by
    simp only [repeCmpsSegAfter, afterStep, finishStep]
    unfold repeCmpsSegSpec
    split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess, afterFetches, beforeFetch,
      resetStepFields]
  have hgs : (repeCmpsSegAfter base n len s).GS = s.GS := by
    simp only [repeCmpsSegAfter, afterStep, finishStep]
    unfold repeCmpsSegSpec
    split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess, afterFetches, beforeFetch,
      resetStepFields]
  obtain ⟨hs, hb⟩ := h
  cases r <;>
  · simp only [SegReg.read, SegReg.select, PrefixSegments.ofState] at hs hb
    exact ⟨by simpa [SegReg.read, SegReg.select, PrefixSegments.ofState, hfs, hgs] using hs,
      by simpa [SegReg.read, SegReg.select, PrefixSegments.ofState, hfs, hgs] using hb⟩

theorem repe_cmpsq_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 8) (hdst : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repeCmpsAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsq_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSpec_cs _ _)
      (by rw [repeCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsq_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 8) (hdst : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repeCmpsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 64
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsq_seg_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hsr hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSegSpec_cs _ _ _)
      (by rw [repeCmpsSegSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsq_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repe_cmpsq_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsd_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 4) (hdst : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repeCmpsAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsd_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSpec_cs _ _)
      (by rw [repeCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsd_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 4) (hdst : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repeCmpsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 32
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsd_seg_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hsr hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSegSpec_cs _ _ _)
      (by rw [repeCmpsSegSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsd_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repe_cmpsd_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsw_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 2) (hdst : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repeCmpsAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsw_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSpec_cs _ _)
      (by rw [repeCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsw_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 2) (hdst : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repeCmpsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 16
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsw_seg_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hsr hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSegSpec_cs _ _ _)
      (by rw [repeCmpsSegSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsw_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repe_cmpsw_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsb_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 1) (hdst : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repeCmpsAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_repe_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsb_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSpec_cs _ _)
      (by rw [repeCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsb_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 1) (hdst : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repeCmpsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 8
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_repe_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsb_seg_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hsr hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSegSpec_cs _ _ _)
      (by rw [repeCmpsSegSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsb_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_repe_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repe_cmpsb_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsq_a32_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 8) (hdst : MemReadable s (rdi.read s) 8)
    (hsl : (rsi.read s).toNat + 8 < 2^32) (hdl : (rdi.read s).toNat + 8 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repeCmpsAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsq_a32_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSpec_cs _ _)
      (by rw [repeCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsq_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repe_cmpsq_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsd_a32_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 4) (hdst : MemReadable s (rdi.read s) 4)
    (hsl : (rsi.read s).toNat + 4 < 2^32) (hdl : (rdi.read s).toNat + 4 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repeCmpsAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsd_a32_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSpec_cs _ _)
      (by rw [repeCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsd_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repe_cmpsd_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsw_a32_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 2) (hdst : MemReadable s (rdi.read s) 2)
    (hsl : (rsi.read s).toNat + 2 < 2^32) (hdl : (rdi.read s).toNat + 2 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repeCmpsAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsw_a32_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSpec_cs _ _)
      (by rw [repeCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsw_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repe_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repe_cmpsw_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsb_a32_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 1) (hdst : MemReadable s (rdi.read s) 1)
    (hsl : (rsi.read s).toNat + 1 < 2^32) (hdl : (rdi.read s).toNat + 1 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repeCmpsAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_repe_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repe_cmpsb_a32_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repeCmpsSpec_cs _ _)
      (by rw [repeCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repe_cmpsb_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_repe_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repe_cmpsb_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
