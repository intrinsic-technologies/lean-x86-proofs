
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Cmps.Generated.Repne.Decode
import X86Proofs.Instructions.Cmps.Generated.Repne.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def repneCmpsAfter (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repneCmpsSpec n
      { t with
        Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := false }

theorem repneCmpsSpec_cs (n : Nat) (t : RamState) : (repneCmpsSpec n t).CS = t.CS := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_efer (n : Nat) (t : RamState) :
    (repneCmpsSpec n t).IA32_EFER = t.IA32_EFER := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_zmm (n : Nat) (t : RamState) : (repneCmpsSpec n t).ZMM = t.ZMM := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_mxcsr (n : Nat) (t : RamState) :
    (repneCmpsSpec n t).MXCSR = t.MXCSR := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_fp87 (n : Nat) (t : RamState) : (repneCmpsSpec n t).FP87 = t.FP87 := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_fsw (n : Nat) (t : RamState) :
    (repneCmpsSpec n t).FP87_Status = t.FP87_Status := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_ftw (n : Nat) (t : RamState) :
    (repneCmpsSpec n t).FP87_Tag_Word = t.FP87_Tag_Word := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_fcw (n : Nat) (t : RamState) :
    (repneCmpsSpec n t).FP87_Control = t.FP87_Control := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_fpuPtr (n : Nat) (t : RamState) :
    fpuPtrOf (repneCmpsSpec n t) = fpuPtrOf t := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess, fpuPtrOf]

theorem repneCmpsSpec_external (n : Nat) (t : RamState) :
    (repneCmpsSpec n t).external = t.external := by
  unfold repneCmpsSpec
  split <;> simp [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_repeat (n : Nat) (t : RamState) :
    (repneCmpsSpec n t).Repeat_String_Operation = repneCmpsCont n t := by
  unfold repneCmpsSpec
  split <;> simp_all

theorem repneCmpsSpec_rflags (n : Nat) (t : RamState) :
    (repneCmpsSpec n t).RFLAGS = if repneCmpsCont n t then t.RFLAGS else
      (cmpSpec ((Operand.mem (rsi.read t) : Operand n).read t)
        ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := by
  unfold repneCmpsSpec
  split <;> simp_all [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_gpr (n : Nat) (t : RamState) :
    (repneCmpsSpec n t).GPR =
      Vector.set (Vector.set (Vector.set t.GPR 6 (t.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (t.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (t.GPR[1] - 1) := by
  unfold repneCmpsSpec
  split <;>
  · simp [cmpsSpec, Operand.write, Operand.read, setFlags, dataAccess, gprIndex, mergeGPR_64,
      Vector.getElem_set]
    rfl

theorem repneCmpsSpec_finish_rip (n : Nat) (t : RamState) (hb : t.Branch_Taken = false)
    (hm : t.«MSRLIST::In_Process» = false) :
    (finishStep (repneCmpsSpec n t)).RIP = if repneCmpsCont n t then t.RIP else t.Next_IP := by
  unfold finishStep repneCmpsSpec
  split <;> simp_all [Operand.write, cmpsSpec, setFlags, dataAccess]

theorem repneCmpsSpec_fixed (n : Nat) (t : RamState) :
    fixedPart (clearRep (repneCmpsSpec n t)) = fixedPart (clearRep t) := by
  unfold repneCmpsSpec
  split <;>
    simp only [fixedPart, clearRep, cmpsSpec, Operand.write, setFlags, dataAccess, beforeFetch,
      resetStepFields, clearStatusFlags_store]

theorem repneCmpsAfter_external (n len : Nat) (s : RamState) :
    (repneCmpsAfter n len s).external = s.external :=
  repneCmpsSpec_external n _

theorem repneCmpsAfter_gpr (n len : Nat) (s : RamState) :
    (repneCmpsAfter n len s).GPR =
      Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (s.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (s.GPR[1] - 1) :=
  repneCmpsSpec_gpr n _

theorem repneCmpsAfter_rsi (n len : Nat) (s : RamState) :
    rsi.read (repneCmpsAfter n len s) = rsi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repneCmpsAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repneCmpsAfter_rdi (n len : Nat) (s : RamState) :
    rdi.read (repneCmpsAfter n len s) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repneCmpsAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repneCmpsAfter_rcx (n len : Nat) (s : RamState) :
    rcx.read (repneCmpsAfter n len s) = rcx.read s - 1 := by
  simp [Operand.read, repneCmpsAfter_gpr, gprIndex]

theorem repneCmpsAfter_repeat (n len : Nat) (s : RamState) :
    (repneCmpsAfter n len s).Repeat_String_Operation = repneCmpsCont n s :=
  repneCmpsSpec_repeat n _

theorem repneCmpsAfter_rflags (n len : Nat) (s : RamState) :
    (repneCmpsAfter n len s).RFLAGS = if repneCmpsCont n s then s.RFLAGS else
      (cmpSpec ((Operand.mem (rsi.read s) : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS :=
  repneCmpsSpec_rflags n _

theorem repneCmpsAfter_rip (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repneCmpsAfter n len s).RIP =
      if repneCmpsCont n s then s.RIP else BitVec.add s.RIP (BitVec.ofNat 64 len) :=
  repneCmpsSpec_finish_rip n _ rfl hmsr

theorem AgreesExcept.repneCmps (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s)
      (clearRep (repneCmpsAfter n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repneCmpsAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6, Ne.symm h7]
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by
        rw [repneCmpsAfter, afterStep, clearRep_ZMM, finishStep_ZMM, repneCmpsSpec_zmm]
        rfl) x
    | mxcsr =>
      show _ = _
      rw [repneCmpsAfter, afterStep, clearRep_MXCSR, finishStep_MXCSR, repneCmpsSpec_mxcsr]
      rfl
    | fpr x =>
      show _ = _
      rw [repneCmpsAfter, afterStep, clearRep_FP87, finishStep_FP87, repneCmpsSpec_fp87]
      rfl
    | fsw =>
      show _ = _
      rw [repneCmpsAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repneCmpsSpec_fsw]
      rfl
    | fcc =>
      show _ = _
      rw [repneCmpsAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repneCmpsSpec_fsw]
      rfl
    | ftw =>
      show _ = _
      rw [repneCmpsAfter, afterStep, clearRep_FP87_Tag_Word, finishStep_FP87_Tag_Word,
        repneCmpsSpec_ftw]
      rfl
    | fcw =>
      show _ = _
      rw [repneCmpsAfter, afterStep, clearRep_FP87_Control, finishStep_FP87_Control,
        repneCmpsSpec_fcw]
      rfl
    | fpuPtr =>
      show _ = _
      rw [repneCmpsAfter, afterStep, fpuPtrOf_clearRep, fpuPtrOf_finishStep, repneCmpsSpec_fpuPtr]
      rfl
    | df =>
      show dfBit (repneCmpsAfter n len s).RFLAGS = dfBit s.RFLAGS
      rw [repneCmpsAfter_rflags]
      split <;> simp only [dfBit_store]
  · simp only [clearRep_external, repneCmpsAfter_external]
  · rw [repneCmpsAfter, afterStep, fixedPart_clearRep_finishStep, repneCmpsSpec_fixed]
    simp only [fixedPart, clearRep, afterFetches, beforeFetch, resetStepFields]
  · simpa [clearRep_external, repneCmpsAfter_external] using hx

theorem ReadyMidRep.repneCmps [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat) :
    ReadyMidRep (repneCmpsAfter n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repneCmpsAfter n len s)).external := by
    rw [clearRep_external, repneCmpsAfter_external]
    exact (ReadyToStep.memory (s := clearRep s) h).tables
  have : ReadyToStep (clearRep (repneCmpsAfter n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repneCmps n len s) htab
  exact this

def repneCmpsSegAfter (base : BitVec 64) (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repneCmpsSegSpec base n
      { t with
        Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := false }

theorem repneCmpsSegSpec_cs (base : BitVec 64) (n : Nat) (t : RamState) : (repneCmpsSegSpec base n t).CS = t.CS := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_efer (base : BitVec 64) (n : Nat) (t : RamState) :
    (repneCmpsSegSpec base n t).IA32_EFER = t.IA32_EFER := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_zmm (base : BitVec 64) (n : Nat) (t : RamState) : (repneCmpsSegSpec base n t).ZMM = t.ZMM := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_mxcsr (base : BitVec 64) (n : Nat) (t : RamState) :
    (repneCmpsSegSpec base n t).MXCSR = t.MXCSR := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_fp87 (base : BitVec 64) (n : Nat) (t : RamState) : (repneCmpsSegSpec base n t).FP87 = t.FP87 := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_fsw (base : BitVec 64) (n : Nat) (t : RamState) :
    (repneCmpsSegSpec base n t).FP87_Status = t.FP87_Status := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_ftw (base : BitVec 64) (n : Nat) (t : RamState) :
    (repneCmpsSegSpec base n t).FP87_Tag_Word = t.FP87_Tag_Word := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_fcw (base : BitVec 64) (n : Nat) (t : RamState) :
    (repneCmpsSegSpec base n t).FP87_Control = t.FP87_Control := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_fpuPtr (base : BitVec 64) (n : Nat) (t : RamState) :
    fpuPtrOf (repneCmpsSegSpec base n t) = fpuPtrOf t := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess, fpuPtrOf]

theorem repneCmpsSegSpec_external (base : BitVec 64) (n : Nat) (t : RamState) :
    (repneCmpsSegSpec base n t).external = t.external := by
  unfold repneCmpsSegSpec
  split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_repeat (base : BitVec 64) (n : Nat) (t : RamState) :
    (repneCmpsSegSpec base n t).Repeat_String_Operation = repneCmpsSegCont base n t := by
  unfold repneCmpsSegSpec
  split <;> simp_all

theorem repneCmpsSegSpec_rflags (base : BitVec 64) (n : Nat) (t : RamState) :
    (repneCmpsSegSpec base n t).RFLAGS = if repneCmpsSegCont base n t then t.RFLAGS else
      (cmpSpec ((Operand.mem (base + rsi.read t) : Operand n).read t)
        ((Operand.mem (rdi.read t) : Operand n).read t)).store t.RFLAGS := by
  unfold repneCmpsSegSpec
  split <;> simp_all [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_gpr (base : BitVec 64) (n : Nat) (t : RamState) :
    (repneCmpsSegSpec base n t).GPR =
      Vector.set (Vector.set (Vector.set t.GPR 6 (t.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (t.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (t.GPR[1] - 1) := by
  unfold repneCmpsSegSpec
  split <;>
  · simp [cmpsSegSpec, Operand.write, Operand.read, setFlags, dataAccess, gprIndex, mergeGPR_64,
      Vector.getElem_set]
    rfl

theorem repneCmpsSegSpec_finish_rip (base : BitVec 64) (n : Nat) (t : RamState) (hb : t.Branch_Taken = false)
    (hm : t.«MSRLIST::In_Process» = false) :
    (finishStep (repneCmpsSegSpec base n t)).RIP = if repneCmpsSegCont base n t then t.RIP else t.Next_IP := by
  unfold finishStep repneCmpsSegSpec
  split <;> simp_all [Operand.write, cmpsSegSpec, setFlags, dataAccess]

theorem repneCmpsSegSpec_fixed (base : BitVec 64) (n : Nat) (t : RamState) :
    fixedPart (clearRep (repneCmpsSegSpec base n t)) = fixedPart (clearRep t) := by
  unfold repneCmpsSegSpec
  split <;>
    simp only [fixedPart, clearRep, cmpsSegSpec, Operand.write, setFlags, dataAccess, beforeFetch,
      resetStepFields, clearStatusFlags_store]

theorem repneCmpsSegAfter_external (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repneCmpsSegAfter base n len s).external = s.external :=
  repneCmpsSegSpec_external base n _

theorem repneCmpsSegAfter_gpr (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repneCmpsSegAfter base n len s).GPR =
      Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (s.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (s.GPR[1] - 1) :=
  repneCmpsSegSpec_gpr base n _

theorem repneCmpsSegAfter_rsi (base : BitVec 64) (n len : Nat) (s : RamState) :
    rsi.read (repneCmpsSegAfter base n len s) = rsi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repneCmpsSegAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repneCmpsSegAfter_rdi (base : BitVec 64) (n len : Nat) (s : RamState) :
    rdi.read (repneCmpsSegAfter base n len s) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repneCmpsSegAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repneCmpsSegAfter_rcx (base : BitVec 64) (n len : Nat) (s : RamState) :
    rcx.read (repneCmpsSegAfter base n len s) = rcx.read s - 1 := by
  simp [Operand.read, repneCmpsSegAfter_gpr, gprIndex]

theorem repneCmpsSegAfter_repeat (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repneCmpsSegAfter base n len s).Repeat_String_Operation = repneCmpsSegCont base n s :=
  repneCmpsSegSpec_repeat base n _

theorem repneCmpsSegAfter_rflags (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repneCmpsSegAfter base n len s).RFLAGS = if repneCmpsSegCont base n s then s.RFLAGS else
      (cmpSpec ((Operand.mem (base + rsi.read s) : Operand n).read s)
        ((Operand.mem (rdi.read s) : Operand n).read s)).store s.RFLAGS :=
  repneCmpsSegSpec_rflags base n _

theorem repneCmpsSegAfter_rip (base : BitVec 64) (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repneCmpsSegAfter base n len s).RIP =
      if repneCmpsSegCont base n s then s.RIP else BitVec.add s.RIP (BitVec.ofNat 64 len) :=
  repneCmpsSegSpec_finish_rip base n _ rfl hmsr

theorem AgreesExcept.repneCmpsSeg (base : BitVec 64) (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .flags, .rip] (clearRep s)
      (clearRep (repneCmpsSegAfter base n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repneCmpsSegAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6, Ne.symm h7]
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by
        rw [repneCmpsSegAfter, afterStep, clearRep_ZMM, finishStep_ZMM, repneCmpsSegSpec_zmm]
        rfl) x
    | mxcsr =>
      show _ = _
      rw [repneCmpsSegAfter, afterStep, clearRep_MXCSR, finishStep_MXCSR, repneCmpsSegSpec_mxcsr]
      rfl
    | fpr x =>
      show _ = _
      rw [repneCmpsSegAfter, afterStep, clearRep_FP87, finishStep_FP87, repneCmpsSegSpec_fp87]
      rfl
    | fsw =>
      show _ = _
      rw [repneCmpsSegAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repneCmpsSegSpec_fsw]
      rfl
    | fcc =>
      show _ = _
      rw [repneCmpsSegAfter, afterStep, clearRep_FP87_Status, finishStep_FP87_Status,
        repneCmpsSegSpec_fsw]
      rfl
    | ftw =>
      show _ = _
      rw [repneCmpsSegAfter, afterStep, clearRep_FP87_Tag_Word, finishStep_FP87_Tag_Word,
        repneCmpsSegSpec_ftw]
      rfl
    | fcw =>
      show _ = _
      rw [repneCmpsSegAfter, afterStep, clearRep_FP87_Control, finishStep_FP87_Control,
        repneCmpsSegSpec_fcw]
      rfl
    | fpuPtr =>
      show _ = _
      rw [repneCmpsSegAfter, afterStep, fpuPtrOf_clearRep, fpuPtrOf_finishStep, repneCmpsSegSpec_fpuPtr]
      rfl
    | df =>
      show dfBit (repneCmpsSegAfter base n len s).RFLAGS = dfBit s.RFLAGS
      rw [repneCmpsSegAfter_rflags]
      split <;> simp only [dfBit_store]
  · simp only [clearRep_external, repneCmpsSegAfter_external]
  · rw [repneCmpsSegAfter, afterStep, fixedPart_clearRep_finishStep, repneCmpsSegSpec_fixed]
    simp only [fixedPart, clearRep, afterFetches, beforeFetch, resetStepFields]
  · simpa [clearRep_external, repneCmpsSegAfter_external] using hx

theorem ReadyMidRep.repneCmpsSeg [Bindings] {s : RamState} (h : ReadyMidRep s) (base : BitVec 64) (n len : Nat) :
    ReadyMidRep (repneCmpsSegAfter base n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repneCmpsSegAfter base n len s)).external := by
    rw [clearRep_external, repneCmpsSegAfter_external]
    exact (ReadyToStep.memory (s := clearRep s) h).tables
  have : ReadyToStep (clearRep (repneCmpsSegAfter base n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repneCmpsSeg base n len s) htab
  exact this

theorem repneCmpsSegAfter_segReady (base : BitVec 64) (n len : Nat) (s : RamState) {r : SegReg} {b : BitVec 64}
    (h : r.Ready b s) : r.Ready b (repneCmpsSegAfter base n len s) := by
  have hfs : (repneCmpsSegAfter base n len s).FS = s.FS := by
    simp only [repneCmpsSegAfter, afterStep, finishStep]
    unfold repneCmpsSegSpec
    split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess, afterFetches, beforeFetch,
      resetStepFields]
  have hgs : (repneCmpsSegAfter base n len s).GS = s.GS := by
    simp only [repneCmpsSegAfter, afterStep, finishStep]
    unfold repneCmpsSegSpec
    split <;> simp [Operand.write, cmpsSegSpec, setFlags, dataAccess, afterFetches, beforeFetch,
      resetStepFields]
  obtain ⟨hs, hb⟩ := h
  cases r <;>
  · simp only [SegReg.read, SegReg.select, PrefixSegments.ofState] at hs hb
    exact ⟨by simpa [SegReg.read, SegReg.select, PrefixSegments.ofState, hfs, hgs] using hs,
      by simpa [SegReg.read, SegReg.select, PrefixSegments.ofState, hfs, hgs] using hb⟩

theorem repne_cmpsq_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 8) (hdst : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repneCmpsAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsq_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSpec_cs _ _)
      (by rw [repneCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsq_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 8) (hdst : MemReadable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repneCmpsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 64
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsq_seg_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hsr hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSegSpec_cs _ _ _)
      (by rw [repneCmpsSegSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsq_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
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
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_cmpsq_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsd_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 4) (hdst : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repneCmpsAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsd_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSpec_cs _ _)
      (by rw [repneCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsd_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 4) (hdst : MemReadable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repneCmpsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 32
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsd_seg_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hsr hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSegSpec_cs _ _ _)
      (by rw [repneCmpsSegSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsd_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
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
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_cmpsd_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsw_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 2) (hdst : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repneCmpsAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsw_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSpec_cs _ _)
      (by rw [repneCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsw_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 2) (hdst : MemReadable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repneCmpsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 16
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsw_seg_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hsr hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSegSpec_cs _ _ _)
      (by rw [repneCmpsSegSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsw_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
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
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_cmpsw_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsb_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 1) (hdst : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repneCmpsAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_repne_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsb_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSpec_cs _ _)
      (by rw [repneCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsb_seg_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = false)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 1) (hdst : MemReadable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repneCmpsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 8
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_repne_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsb_seg_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hsr hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSegSpec_cs _ _ _)
      (by rw [repneCmpsSegSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsb_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
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
  have hdecode := decodeLegacy0_run_of_A6_repne_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_cmpsb_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsq_a32_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 8) (hdst : MemReadable s (rdi.read s) 8)
    (hsl : (rsi.read s).toNat + 8 < 2^32) (hdl : (rdi.read s).toNat + 8 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repneCmpsAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsq_a32_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSpec_cs _ _)
      (by rw [repneCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsq_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
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
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_cmpsq_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsd_a32_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 4) (hdst : MemReadable s (rdi.read s) 4)
    (hsl : (rsi.read s).toNat + 4 < 2^32) (hdl : (rdi.read s).toNat + 4 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repneCmpsAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsd_a32_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSpec_cs _ _)
      (by rw [repneCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsd_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
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
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_cmpsd_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsw_a32_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA7]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 2) (hdst : MemReadable s (rdi.read s) 2)
    (hsl : (rsi.read s).toNat + 2 < 2^32) (hdl : (rdi.read s).toNat + 2 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repneCmpsAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA7]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA7]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsw_a32_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSpec_cs _ _)
      (by rw [repneCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsw_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
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
  have hdecode := decodeLegacy0_run_of_A7_repne_cmpsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_cmpsw_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA7 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA7 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsb_a32_step [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (s : RamState) (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hasz : (scanContext s.DS (PrefixSegments.ofState s) pre).asz_prefix_present = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA6]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : MemReadable s (rsi.read s) 1) (hdst : MemReadable s (rdi.read s) 1)
    (hsl : (rsi.read s).toNat + 1 < 2^32) (hdl : (rdi.read s).toNat + 1 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repneCmpsAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA6]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA6]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A6_repne_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [repne_cmpsb_a32_form hcm (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) hlock hseg hm64 hasz
    hcpu.ds hcpu.es hdf hcount (hsrc.of_external_eq rfl) (hdst.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq (repneCmpsSpec_cs _ _)
      (by rw [repneCmpsSpec_efer]))
  rw [hpreserve] at hstep
  exact hstep

theorem repne_cmpsb_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 242)
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
  have hdecode := decodeLegacy0_run_of_A6_repne_cmpsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [repne_cmpsb_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ hlock hm64 hasz
    hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA6 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA6 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
