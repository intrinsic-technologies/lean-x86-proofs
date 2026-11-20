import X86Proofs.Program.ReadWrite.Mmx
import X86Proofs.Step.X87

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

@[simp] theorem afterFetches_FP87_Tag_Word (s : RamState) (k : Nat) :
    (afterFetches s k).FP87_Tag_Word = s.FP87_Tag_Word := rfl

@[simp] theorem beforeFetch_FP87_Tag_Word (s : RamState) :
    (beforeFetch s).FP87_Tag_Word = s.FP87_Tag_Word := rfl

@[simp] theorem afterFetches_FP87_Control (s : RamState) (k : Nat) :
    (afterFetches s k).FP87_Control = s.FP87_Control := rfl

@[simp] theorem beforeFetch_FP87_Control (s : RamState) :
    (beforeFetch s).FP87_Control = s.FP87_Control := rfl

/-- The precondition of an x87 register-stack triple at `p` with stack top `top`: RIP = `p`,
`CR0.EM` and `CR0.TS` clear (no #NM), no pending unmasked exception (FSW.ES clear, no #MF), every
exception masked in the control word (an instruction only ORs the exception flags into the status
word, so ES stays clear), a processor that updates the data pointer only on exceptions (CPUID
FDP_EXCPTN_ONLY: a register form leaves FDP, FDS and FOP alone instead of drawing FDP and FDS from
the oracle), and TOP = `top`. The tag conditions of each form (its sources not empty, a pushed slot
empty: no stack fault) are separate conjuncts of its triple's precondition. -/
structure X87Pre [Bindings] (p : BitVec 64) (top : BitVec 3) (s : RamState) : Prop where
  rip : s.RIP = p
  cr0 : Prelude.CR0.SSEEnabled s.CR0
  es : fswES s.FP87_Status = 0
  fcw : FcwMasked s.FP87_Control
  fdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true
  top : fswTop s.FP87_Status = top

/-- The last-instruction pointers with FIP and FCS replaced (FDP, FDS and FOP kept). -/
def x87Ptr (ptr : BitVec 171) (fip : BitVec 64) (fcs : BitVec 16) : BitVec 171 :=
  ptr.extractLsb' 80 91 ++ fcs ++ fip

theorem fpuPtrOf_fip_fcs (t : RamState) (fip : BitVec 64) (fcs : BitVec 16) :
    fpuPtrOf { t with FP87_FCS := fcs, FP87_FIP := fip } = x87Ptr (fpuPtrOf t) fip fcs := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fpuPtrOf, x87Ptr, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', Int.reduceToNat]
  by_cases h1 : i < 64
  · simp only [h1, ↓reduceIte]
  by_cases h2 : i - 64 < 16
  · simp only [h1, h2, ↓reduceIte]
  have h3 : i - 64 - 16 < 91 := by omega
  simp only [h1, h2, h3, ↓reduceIte, decide_true, Bool.true_and,
    show ¬ (80 + (i - 64 - 16) < 64) by omega, show ¬ (80 + (i - 64 - 16) - 64 < 16) by omega]
  by_cases h4 : i - 64 - 16 < 64
  · simp only [h4, ↓reduceIte, show 80 + (i - 64 - 16) - 64 - 16 < 64 by omega]
    exact congrArg _ (by omega)
  · simp only [h4, ↓reduceIte, show ¬ (80 + (i - 64 - 16) - 64 - 16 < 64) by omega]
    by_cases h5 : i - 64 - 16 - 64 < 16
    · simp only [h5, ↓reduceIte, show 80 + (i - 64 - 16) - 64 - 16 - 64 < 16 by omega]
      exact congrArg _ (by omega)
    · simp only [h5, ↓reduceIte, show ¬ (80 + (i - 64 - 16) - 64 - 16 - 64 < 16) by omega]
      exact congrArg _ (by omega)

/-- What a register-stack x87 form leaves from the state `t` it starts from: `Next_IP` := `ip`,
`k` oracle bits used up, the physical registers `fp`, the tag word `ftw`, the status word `fsw`,
and FCS := the code segment's selector, FIP := RIP (`FP87.Update_Instruction_Info`). -/
def x87Out (t : RamState) (ip : BitVec 64) (k : Nat) (fp : X86.Runtime.Array 8 F80_Type)
    (ftw fsw : BitVec 16) : RamState :=
  { t with
    Next_IP := ip
    oracle := oracleSkip t.oracle k
    FP87 := fp
    FP87_Tag_Word := ftw
    FP87_Status := fsw
    FP87_FCS := t.CS.selector
    FP87_FIP := t.RIP }

section x87Out

variable (t : RamState) (ip : BitVec 64) (k : Nat) (fp : X86.Runtime.Array 8 F80_Type)
  (ftw fsw : BitVec 16)

@[simp] theorem x87Out_FP87 : (x87Out t ip k fp ftw fsw).FP87 = fp := rfl
@[simp] theorem x87Out_FP87_Tag_Word : (x87Out t ip k fp ftw fsw).FP87_Tag_Word = ftw := rfl
@[simp] theorem x87Out_FP87_Status : (x87Out t ip k fp ftw fsw).FP87_Status = fsw := rfl
theorem fpuPtrOf_x87Out :
    fpuPtrOf (x87Out t ip k fp ftw fsw) = x87Ptr (fpuPtrOf t) t.RIP t.CS.selector := by
  rw [← fpuPtrOf_fip_fcs]
  rfl

end x87Out

theorem AgreesExcept.afterStep_x87 (s : RamState) (length : Nat) (ip : BitVec 64)
    (k : RamState → Nat) (rs : List (BitVec 3)) (fp : RamState → X86.Runtime.Array 8 F80_Type)
    (ftw fsw : RamState → BitVec 16)
    (hfp : ∀ r : BitVec 3, r ∉ rs →
      (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex r] = s.FP87[fprIndex r]) :
    AgreesExcept (rs.map Component.fpr ++ [.ftw, .fsw, .fcc, .fpuPtr, .rip]) s
      (afterStep s length fun t => x87Out t ip (k t) (fp t) (ftw t) (fsw t)) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | fpr r =>
      have hr : r ∉ rs := fun hm => hc (List.mem_append_left _ (List.mem_map_of_mem hm))
      exact hfp r hr
    | ftw => exact absurd (by simp) hc
    | fsw => exact absurd (by simp) hc
    | fcc => exact absurd (by simp) hc
    | fpuPtr => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · simp only [fixedPart, afterStep, finishStep, x87Out, afterFetches, beforeFetch,
      resetStepFields]

theorem afterStep_x87_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (ip : BitVec 64) (k : RamState → Nat) (fp : RamState → X86.Runtime.Array 8 F80_Type)
    (ftw fsw : RamState → BitVec 16) :
    (afterStep s length fun t => x87Out t ip (k t) (fp t) (ftw t) (fsw t)).RIP = ip := by
  simp [afterStep, finishStep, x87Out, afterFetches, beforeFetch, resetStepFields,
    h.ready.repeatClear, h.ready.msr]

/-- The effect of an x87 register-stack step at `p` of `len` bytes: the physical registers
`regs` written (each with its value), the tag word := `ftw`, the status word without its condition
codes := `fsw`, the condition codes selected by `m` := `cc` (the others undefined), FIP := `p` and
FCS := the code segment's selector (FDP, FDS, FOP kept). -/
def x87Effect (p : BitVec 64) (len : Nat) (regs : List (BitVec 3 × BitVec 80))
    (ftw fsw : BitVec 16) (m cc : BitVec 4) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := regs.map (fun rv => (⟨(Operand.fpr rv.1 : Operand 80), rv.2⟩ : Write)) ++
      [⟨(Operand.ftw : Operand 16), ftw⟩, ⟨(Operand.fsw : Operand 16), fsw⟩,
        ⟨(Operand.fcc m : Operand 4), cc⟩,
        ⟨(Operand.fpuPtr : Operand 171),
          x87Ptr ((Operand.fpuPtr : Operand 171).read s) p s.CS.selector⟩] }

theorem x87Effect_components (p : BitVec 64) (len : Nat) (regs : List (BitVec 3 × BitVec 80))
    (ftw fsw : BitVec 16) (m cc : BitVec 4) (s : RamState) :
    (x87Effect p len regs ftw fsw m cc s).components =
      (regs.map Prod.fst).map Component.fpr ++ [.ftw, .fsw, .fcc, .fpuPtr, .rip] := by
  simp [x87Effect, Effect.components, Function.comp_def]

/-- A step whose form ends in `x87Out` has an `x87Effect`, given the values the form leaves. -/
theorem x87Effect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (p : BitVec 64) (hp : s.RIP = p) (k : RamState → Nat) (regs : List (BitVec 3 × BitVec 80))
    (fp : RamState → X86.Runtime.Array 8 F80_Type) (ftw fsw : RamState → BitVec 16)
    (ftwV fswV : BitVec 16) (m cc : BitVec 4)
    (hregs : ∀ rv ∈ regs, (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex rv.1] = rv.2)
    (hfp : ∀ r : BitVec 3, r ∉ regs.map Prod.fst →
      (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex r] = s.FP87[fprIndex r])
    (hftw : ftw (afterFetches (beforeFetch s) (length + 1)) = ftwV)
    (hfsw : fswRest (fsw (afterFetches (beforeFetch s) (length + 1))) = fswV)
    (hcc : fswCC (fsw (afterFetches (beforeFetch s) (length + 1))) &&& m = cc) :
    (x87Effect p length regs ftwV fswV m cc s).Holds s
      (afterStep s length fun t =>
        x87Out t (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t)) := by
  refine ⟨afterStep_x87_rip h _ _ _ _ _ _, ?_, trivial, ?_⟩
  · rw [Write.allHold_iff]
    intro w hw
    rw [Operand.read_afterStep]
    simp only [x87Effect, List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff,
      or_false] at hw
    rcases hw with ⟨rv, hrv, rfl⟩ | rfl | rfl | rfl | rfl
    · simp only [Operand.read_fpr, x87Out_FP87]
      exact hregs rv hrv
    · simp only [Operand.read_ftw, x87Out_FP87_Tag_Word]
      exact hftw
    · simp only [Operand.read_fsw, x87Out_FP87_Status]
      exact hfsw
    · simp only [Operand.read_fcc, x87Out_FP87_Status]
      exact hcc
    · simp only [Operand.read_fpuPtr, fpuPtrOf_x87Out, ← hp]
      rfl
  · rw [x87Effect_components]
    exact AgreesExcept.afterStep_x87 s length _ k _ fp ftw fsw hfp

/-! ### Forms that also set the status flags (FCOMI, FUCOMI and their popping forms) -/

/-- `x87Out` with the status flags of RFLAGS := `f`. -/
def x87OutF (t : RamState) (ip : BitVec 64) (k : Nat) (fp : X86.Runtime.Array 8 F80_Type)
    (ftw fsw : BitVec 16) (f : StatusFlags) : RamState :=
  { x87Out t ip k fp ftw fsw with RFLAGS := f.store t.RFLAGS }

theorem fpuPtrOf_x87OutF (t : RamState) (ip : BitVec 64) (k : Nat)
    (fp : X86.Runtime.Array 8 F80_Type) (ftw fsw : BitVec 16) (f : StatusFlags) :
    fpuPtrOf (x87OutF t ip k fp ftw fsw f) = x87Ptr (fpuPtrOf t) t.RIP t.CS.selector := by
  rw [← fpuPtrOf_fip_fcs]
  rfl

theorem ofRFLAGS_afterStep_x87F (s : RamState) (length : Nat) (ip : BitVec 64) (k : RamState → Nat)
    (fp : RamState → X86.Runtime.Array 8 F80_Type) (ftw fsw : RamState → BitVec 16)
    (f : RamState → StatusFlags) :
    StatusFlags.ofRFLAGS (afterStep s length fun t =>
      x87OutF t ip (k t) (fp t) (ftw t) (fsw t) (f t)).RFLAGS =
      f (afterFetches (beforeFetch s) (length + 1)) := by
  simp [afterStep, finishStep, x87OutF, StatusFlags.ofRFLAGS_store]

theorem AgreesExcept.afterStep_x87F (s : RamState) (length : Nat) (ip : BitVec 64)
    (k : RamState → Nat)
    (rs : List (BitVec 3)) (fp : RamState → X86.Runtime.Array 8 F80_Type)
    (ftw fsw : RamState → BitVec 16) (f : RamState → StatusFlags)
    (hfp : ∀ r : BitVec 3, r ∉ rs →
      (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex r] = s.FP87[fprIndex r]) :
    AgreesExcept (rs.map Component.fpr ++ [.ftw, .fsw, .fcc, .fpuPtr, .flags, .rip]) s
      (afterStep s length fun t => x87OutF t ip (k t) (fp t) (ftw t) (fsw t) (f t)) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | fpr r =>
      have hr : r ∉ rs := fun hm => hc (List.mem_append_left _ (List.mem_map_of_mem hm))
      exact hfp r hr
    | ftw => exact absurd (by simp) hc
    | fsw => exact absurd (by simp) hc
    | fcc => exact absurd (by simp) hc
    | fpuPtr => exact absurd (by simp) hc
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | df => exact dfBit_store _ _
    | _ => rfl
  · simp only [fixedPart, afterStep, finishStep, x87OutF, x87Out, afterFetches, beforeFetch,
      resetStepFields, clearStatusFlags_store]

theorem afterStep_x87F_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (ip : BitVec 64) (k : RamState → Nat) (fp : RamState → X86.Runtime.Array 8 F80_Type)
    (ftw fsw : RamState → BitVec 16) (f : RamState → StatusFlags) :
    (afterStep s length fun t => x87OutF t ip (k t) (fp t) (ftw t) (fsw t) (f t)).RIP = ip := by
  simp [afterStep, finishStep, x87OutF, x87Out, afterFetches, beforeFetch, resetStepFields,
    h.ready.repeatClear, h.ready.msr]

/-- `x87Effect` that also sets the status flags to `f`. -/
def x87FlagsEffect (p : BitVec 64) (len : Nat) (regs : List (BitVec 3 × BitVec 80))
    (ftw fsw : BitVec 16) (m cc : BitVec 4) (f : StatusFlags) (s : RamState) : Effect :=
  { x87Effect p len regs ftw fsw m cc s with flags := some (.ofStatusFlags f) }

theorem x87FlagsEffect_components (p : BitVec 64) (len : Nat)
    (regs : List (BitVec 3 × BitVec 80)) (ftw fsw : BitVec 16) (m cc : BitVec 4)
    (f : StatusFlags) (s : RamState) :
    (x87FlagsEffect p len regs ftw fsw m cc f s).components =
      (regs.map Prod.fst).map Component.fpr ++ [.ftw, .fsw, .fcc, .fpuPtr, .flags, .rip] := by
  simp [x87FlagsEffect, x87Effect, Effect.components, Function.comp_def]

/-- A step whose form ends in `x87OutF` has an `x87FlagsEffect`, given the values it leaves. -/
theorem x87FlagsEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (p : BitVec 64) (hp : s.RIP = p) (k : RamState → Nat) (regs : List (BitVec 3 × BitVec 80))
    (fp : RamState → X86.Runtime.Array 8 F80_Type) (ftw fsw : RamState → BitVec 16)
    (f : RamState → StatusFlags) (ftwV fswV : BitVec 16) (m cc : BitVec 4) (fV : StatusFlags)
    (hregs : ∀ rv ∈ regs, (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex rv.1] = rv.2)
    (hfp : ∀ r : BitVec 3, r ∉ regs.map Prod.fst →
      (fp (afterFetches (beforeFetch s) (length + 1)))[fprIndex r] = s.FP87[fprIndex r])
    (hftw : ftw (afterFetches (beforeFetch s) (length + 1)) = ftwV)
    (hfsw : fswRest (fsw (afterFetches (beforeFetch s) (length + 1))) = fswV)
    (hcc : fswCC (fsw (afterFetches (beforeFetch s) (length + 1))) &&& m = cc)
    (hf : f (afterFetches (beforeFetch s) (length + 1)) = fV) :
    (x87FlagsEffect p length regs ftwV fswV m cc fV s).Holds s
      (afterStep s length fun t =>
        x87OutF t (BitVec.add p (BitVec.ofNat 64 length)) (k t) (fp t) (ftw t) (fsw t)
          (f t)) := by
  refine ⟨afterStep_x87F_rip h _ _ _ _ _ _ _, ?_, ?_, ?_⟩
  · rw [Write.allHold_iff]
    intro w hw
    rw [Operand.read_afterStep]
    simp only [x87FlagsEffect, x87Effect, List.mem_append, List.mem_map, List.mem_cons,
      List.mem_nil_iff, or_false] at hw
    rcases hw with ⟨rv, hrv, rfl⟩ | rfl | rfl | rfl | rfl
    · simp only [Operand.read_fpr]
      exact hregs rv hrv
    · simp only [Operand.read_ftw]
      exact hftw
    · simp only [Operand.read_fsw]
      exact hfsw
    · simp only [Operand.read_fcc]
      exact hcc
    · simp only [Operand.read_fpuPtr, fpuPtrOf_x87OutF, ← hp]
      rfl
  · show StatusFlagsOutcome.Allows _ _
    rw [ofRFLAGS_afterStep_x87F, hf]
    exact StatusFlagsOutcome.allows_ofStatusFlags _
  · rw [x87FlagsEffect_components]
    exact AgreesExcept.afterStep_x87F s length _ k _ fp ftw fsw f hfp

/-! ### Control forms: FWAIT, FNCLEX, FNSTSW AX, FNINIT

These forms do not call `FP87.Update_Instruction_Info`: FIP and FCS are kept (FNINIT clears every
last-instruction pointer). -/

/-- What FWAIT, FNCLEX and FNSTSW AX leave (before FNSTSW's write of AX) from the state `t` they
start from: `Next_IP` := `ip`, `k` oracle bits used up, the status word `fsw`. -/
def x87CtlOut (t : RamState) (ip : BitVec 64) (k : Nat) (fsw : BitVec 16) : RamState :=
  { t with Next_IP := ip, oracle := oracleSkip t.oracle k, FP87_Status := fsw }

/-- What FNINIT leaves from the state `t` it starts from: `Next_IP` := `ip`, the control word
`fcw`, status word 0, every tag empty, the last-instruction pointers 0. -/
def x87InitOut (t : RamState) (ip : BitVec 64) (fcw : BitVec 16) : RamState :=
  { t with
    Next_IP := ip
    FP87_Control := fcw
    FP87_Status := 0
    FP87_Tag_Word := 0xFFFF
    FP87_FDP := 0
    FP87_FIP := 0
    FP87_FCS := 0
    FP87_FDS := 0
    FP87_FOP := 0 }

theorem afterStep_x87Ctl_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (ip : BitVec 64) (k : Nat) (fsw : RamState → BitVec 16) :
    (afterStep s length fun t => x87CtlOut t ip k (fsw t)).RIP = ip := by
  simp [afterStep, finishStep, x87CtlOut, afterFetches, beforeFetch, resetStepFields,
    h.ready.repeatClear, h.ready.msr]

theorem afterStep_x87Stsw_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (ip : BitVec 64) (k : Nat) (fsw v : RamState → BitVec 16) :
    (afterStep s length fun t =>
      (Operand.reg 0 : Operand 16).write (x87CtlOut t ip k (fsw t)) (v t)).RIP = ip := by
  simp [afterStep, finishStep, x87CtlOut, Operand.write, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem afterStep_x87Init_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (ip : BitVec 64) (fcw : RamState → BitVec 16) :
    (afterStep s length fun t => x87InitOut t ip (fcw t)).RIP = ip := by
  simp [afterStep, finishStep, x87InitOut, afterFetches, beforeFetch, resetStepFields,
    h.ready.repeatClear, h.ready.msr]

/-- FWAIT changes only the condition codes (and RIP). -/
theorem AgreesExcept.afterStep_x87Ctl_cc (s : RamState) (length : Nat) (ip : BitVec 64) (k : Nat)
    (fsw : RamState → BitVec 16)
    (hrest : fswRest (fsw (afterFetches (beforeFetch s) (length + 1))) = fswRest s.FP87_Status) :
    AgreesExcept [.fcc, .rip] s (afterStep s length fun t => x87CtlOut t ip k (fsw t)) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | fsw => exact hrest
    | fcc => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | _ => rfl
  · simp only [fixedPart, afterStep, finishStep, x87CtlOut, afterFetches, beforeFetch,
      resetStepFields]

/-- FNCLEX changes only the status word (and RIP). -/
theorem AgreesExcept.afterStep_x87Ctl (s : RamState) (length : Nat) (ip : BitVec 64) (k : Nat)
    (fsw : RamState → BitVec 16) :
    AgreesExcept [.fsw, .fcc, .rip] s (afterStep s length fun t => x87CtlOut t ip k (fsw t)) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | fsw => exact absurd (by simp) hc
    | fcc => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | _ => rfl
  · simp only [fixedPart, afterStep, finishStep, x87CtlOut, afterFetches, beforeFetch,
      resetStepFields]

/-- FNSTSW AX changes only AX, the condition codes (and RIP). -/
theorem AgreesExcept.afterStep_x87Stsw (s : RamState) (length : Nat) (ip : BitVec 64) (k : Nat)
    (fsw : RamState → BitVec 16) (v : RamState → BitVec 16)
    (hrest : fswRest (fsw (afterFetches (beforeFetch s) (length + 1))) = fswRest s.FP87_Status) :
    AgreesExcept [.reg 0, .fcc, .rip] s (afterStep s length fun t =>
      (Operand.reg 0 : Operand 16).write (x87CtlOut t ip k (fsw t)) (v t)) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      have hne : (0 : BitVec 5) ≠ r := fun h => hc (h ▸ List.mem_cons_self)
      have := (Operand.read_afterStep s length (fun t =>
        (Operand.reg 0 : Operand 16).write (x87CtlOut t ip k (fsw t)) (v t))
        (.reg r : Operand 64)).trans (Operand.read_write_reg_of_ne (m := 64) _ hne _)
      simp only [Operand.read_reg64] at this
      exact this
    | fsw => exact hrest
    | fcc => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | _ => rfl
  · simp only [fixedPart, afterStep, finishStep, x87CtlOut, Operand.write, afterFetches,
      beforeFetch, resetStepFields]

/-- FNINIT changes only the x87 control, status and tag words and last-instruction pointers (and
RIP). -/
theorem AgreesExcept.afterStep_x87Init (s : RamState) (length : Nat) (ip : BitVec 64)
    (fcw : RamState → BitVec 16) :
    AgreesExcept [.fcw, .fsw, .fcc, .ftw, .fpuPtr, .rip] s
      (afterStep s length fun t => x87InitOut t ip (fcw t)) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | fcw => exact absurd (by simp) hc
    | fsw => exact absurd (by simp) hc
    | fcc => exact absurd (by simp) hc
    | ftw => exact absurd (by simp) hc
    | fpuPtr => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | _ => rfl
  · simp only [fixedPart, afterStep, finishStep, x87InitOut, afterFetches, beforeFetch,
      resetStepFields]

theorem Operand.read_reg64_write_reg16 {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (r : BitVec 5) (v : BitVec 16) :
    (Operand.reg r : Operand 64).read ((Operand.reg r : Operand 16).write s v) =
      mergeGPR 16 v ((Operand.reg r : Operand 64).read s) := by
  simp [Operand.write, Operand.read]

theorem cc_and_15 (x : BitVec 4) : x &&& (15 : BitVec 4) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt4_cases hi with rfl | rfl | rfl | rfl <;> simp

/-- The normalization the x87 triples use on what a step leaves: reads of the state after the
fetches, register-stack updates, and the parts of the status word. -/
macro "x87_simp" : tactic => `(tactic|
  simp only [afterFetches_FP87, beforeFetch_FP87, afterFetches_FP87_Status,
    beforeFetch_FP87_Status, afterFetches_FP87_Tag_Word, beforeFetch_FP87_Tag_Word,
    afterFetches_FP87_Control, beforeFetch_FP87_Control, Operand.read_fpr, Operand.read_ftw,
    Operand.read_fsw, Operand.read_fcw, fprSet_get_self, fswRest_fswSetTop, fswRest_fswC1Zero,
    fswRest_fswSetC, fswCC_fswSetTop, fswCC_fswOrFlags, fswCC_fswSetC, fswOrFlags_zero,
    fswTop_fswSetTop, fswTop_fswC1Zero, add_zero3, add_zero3'])

attribute [x86_compose] x87Effect x87FlagsEffect x87Ptr

/-! ### Normalizing composed x87 effects -/

/-- FCS and FDP, FDS, FOP of `x87Ptr`'s result are its inputs' (a second `x87Ptr` keeps them). -/
@[x86_compose] theorem extractLsb'_x87Ptr (x : BitVec 91) (cs : BitVec 16) (ip : BitVec 64) :
    (x ++ cs ++ ip).extractLsb' 80 91 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp only [show ¬ (80 + i < 64) by omega, show ¬ (80 + i - 64 < 16) by omega, ite_false]
  exact congrArg _ (by omega)

/-- The status word read as an operand is already without its condition codes. -/
@[x86_compose] theorem fswRest_read_fsw (t : RamState) :
    fswRest ((Operand.fsw : Operand 16).read t) = (Operand.fsw : Operand 16).read t := by
  simp only [Operand.read_fsw, fswRest_fswRest]

theorem fswRest_fswOrFlags (f : BitVec 16) (x : BitVec 6) :
    fswRest (fswOrFlags f x) = fswOrFlags (fswRest f) x := by
  unfold fswOrFlags
  fsw_bits

attribute [x86_compose] fswRest_fswSetTop fswRest_fswOrFlags add_zero3 add_zero3'

/-! ### Preconditions after an effect -/

@[simp] theorem fswTop_fswRest (f : BitVec 16) : fswTop (fswRest f) = fswTop f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [fswTop, fswRest]

/-- The tag word after an effect, read off the canonical state. -/
theorem X87Pre.ftw_of_obs {e : Effect} {s s' : RamState} (ho : Obs (e.after s true) s') :
    s'.FP87_Tag_Word = (Operand.ftw : Operand 16).read (e.after s true) :=
  ho.ftw.symm

/-- A physical register after an effect, read off the canonical state. -/
theorem X87Pre.fpr_of_obs {e : Effect} {s s' : RamState} (ho : Obs (e.after s true) s')
    (r : BitVec 3) : s'.FP87[fprIndex r] = (Operand.fpr r : Operand 80).read (e.after s true) :=
  (congrArg (·[fprIndex r]) ho.fpr).symm

/-- The control word after an effect, read off the canonical state. -/
theorem X87Pre.fcw_of_obs {e : Effect} {s s' : RamState} (ho : Obs (e.after s true) s') :
    s'.FP87_Control = (Operand.fcw : Operand 16).read (e.after s true) :=
  ho.fcw.symm

/-! ### Carry-over lemmas -/

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre_simp] theorem fswTop_field (t : RamState) :
    fswTop t.FP87_Status = fswTop ((Operand.fsw : Operand 16).read t) := by
  simp [Operand.read]

attribute [x86_pre_simp] fswTop_fswSetTop fswTop_fswOrFlags fswES_fswSetTop fswES_fswOrFlags
  ftwTag_ftwSet_self fswES_fswRest fswTop_fswRest fswES_mmxStatus

@[x86_pre_simp] theorem x87Tag_eq_three (v : BitVec 80) : x87Tag v = 3#2 ↔ False :=
  ⟨x87Tag_ne_three v, False.elim⟩

@[x86_pre_simp] theorem fcwMasked_field (t : RamState) :
    FcwMasked t.FP87_Control ↔ FcwMasked ((Operand.fcw : Operand 16).read t) := by
  simp [Operand.read]

@[x86_pre] theorem X87Pre.of_holds [Bindings] (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p : BitVec 64} {top : BitVec 3} (hrip : e.rip = p) (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES ((Operand.fsw : Operand 16).read (e.after s true)) = 0)
    (hfcw : FcwMasked ((Operand.fcw : Operand 16).read (e.after s true)))
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true)
    (htop : fswTop ((Operand.fsw : Operand 16).read (e.after s true)) = top) :
    X87Pre p top s' := by
  refine ⟨h.rip_of hrip, h.CR0_eq ▸ hcr0, fswES_of_obs ho hes, ?_,
    h.reportsCPUFeature_iff.mpr hfdp, ?_⟩
  · rw [← ho.fcw]
    simpa [Operand.read] using hfcw
  · rw [← fswTop_fswRest, ← ho.fsw]
    simpa [Operand.read] using htop

end Carry

end X86Proofs
