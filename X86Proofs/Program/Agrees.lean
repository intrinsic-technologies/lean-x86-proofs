import X86Proofs.Step.AfterStep
import X86Proofs.Program.Code

/-!
# Agreeing except on some components

`AgreesExcept cs s s'`: the state `s'` is `s` except possibly on the components listed in `cs`
(general-purpose registers, the six status flags, the direction flag, RIP, byte ranges of memory,
XMM registers, MXCSR, the x87 registers, status word, condition codes, tag and control words and
last-instruction pointers) and on the per-step bookkeeping every step changes (the oracle,
`Next_IP`,
lean-x86's trace of memory accesses, and the fields lean-x86 resets at the start of each step). In
particular every byte of memory outside the listed ranges, the control registers, the segment
registers, the bits of RFLAGS other than the status flags and DF (TF, IF, IOPL, NT, RF, AC, ID, …)
and bits 128–511 of every ZMM register are equal, and no byte of RAM disappears
(`grow`: a byte a store wrote is still present for a later access). It is what a triple's
postcondition says about everything an instruction doesn't write.

- `AgreesExcept.refl`, `AgreesExcept.trans` (except `cs₁`, then except `cs₂`, gives except
  `cs₁ ++ cs₂`), `AgreesExcept.narrow` (drop components that turned out to agree after all).
- `AgreesExcept.read`, `AgreesExcept.read_xmm`, `AgreesExcept.byte`, `AgreesExcept.external`:
  register reads outside `cs`, bytes outside the listed ranges, and (if no range is listed) all of
  memory are preserved; `AgreesExcept.mxcsr`: MXCSR, if `.mxcsr` is not listed;
  `AgreesExcept.fpr`, `AgreesExcept.fsw`, `AgreesExcept.fcc`, `AgreesExcept.fswAll`,
  `AgreesExcept.ftw`, `AgreesExcept.fcw`, `AgreesExcept.fpuPtr`: the x87 state outside `cs`;
  `AgreesExcept.statusFlags`, `AgreesExcept.df`, `AgreesExcept.rflags`: the status flags, DF, and
  all of RFLAGS if neither is listed.
- `CodeIn.of_agreesExcept`: code outside the listed ranges stays in memory.
- `AgreesExcept.afterStep_writeOutputs`: a step whose form ends in `writeOutputs` to register `r`
  changes only `r`, the flags and RIP.
- `AgreesExcept.afterStep_writeFlagsOutputs`: a step whose form ends in `writeFlagsOutputs` changes only the
  flags and RIP.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/-- A part of the state an instruction may write: a *location* (as in Dafny's and
Vale's `modifies` clauses). A list of them is a write
*footprint* (`Effect.components`, `AgreesExcept`). -/
inductive Component where
  /-- General-purpose register number `r` (all 64 bits). -/
  | reg (r : BitVec 5)
  /-- The six status flags CF, PF, AF, ZF, SF, OF (RFLAGS bits `statusFlagBits`). -/
  | flags
  /-- The direction flag DF (RFLAGS bit 10, `dfBit`): written by CLD, STD and POPF, read by the
  string instructions. The other non-status bits of RFLAGS are always kept (`fixedPart`). -/
  | df
  /-- The instruction pointer. -/
  | rip
  /-- The `len` bytes of memory at `addr`, `addr + 1`, … (physical addresses, wrapping at
  2^64). -/
  | mem (addr : BitVec 64) (len : Nat)
  /-- XMM register number `r`: the low 128 bits of ZMM register `r`. Bits 128–511 are not part of
  it: they are always kept (`fixedPart`), as legacy SSE writes keep them. -/
  | xmm (r : BitVec 5)
  /-- The SSE control and status register MXCSR (all 32 bits): written by the floating-point SSE
  forms (the sticky exception flags) and by LDMXCSR. -/
  | mxcsr
  /-- Physical x87 register R`r` (all 80 bits, `State.FP87`): written by the MMX forms (MMX
  register `r` is its low 64 bits) and the x87 forms. -/
  | fpr (r : BitVec 3)
  /-- The x87 status word FSW except its condition codes (the stack top TOP, the exception flags,
  SF, ES, B; `fswRest`): every MMX form sets TOP to 0. -/
  | fsw
  /-- The x87 condition codes C0–C3 (FSW bits 8, 9, 10, 14; `fswCC`), which most x87 instructions
  leave partly undefined. -/
  | fcc
  /-- The x87 tag word FTW: every MMX form sets it to 0 (all valid), EMMS to `0xFFFF` (all
  empty). -/
  | ftw
  /-- The x87 control word FCW. -/
  | fcw
  /-- The x87 last-instruction pointers FIP, FCS, FDP, FDS and FOP (`fpuPtrOf`). -/
  | fpuPtr
  deriving DecidableEq

/-- The component an operand lives in: its register (for AH–BH, the register they are part of), or
its `n / 8` bytes of memory. -/
def Operand.component {n : Nat} : Operand n → Component
  | .reg r => .reg r
  | .mem addr => .mem addr (n / 8)
  | .xmm r => .xmm r
  | .regHigh r => .reg r
  | .mxcsr => .mxcsr
  | .df => .df
  | .fpr r => .fpr r
  | .mmx r => .fpr r
  | .fsw => .fsw
  | .ftw => .ftw
  | .fcw => .fcw
  | .fpuPtr => .fpuPtr
  | .fcc _ => .fcc

/-- `c` is a memory component. Memory components are compared byte by byte (`AgreesExcept.memory`),
since a write may overlap a range without being that range. -/
def Component.isMem : Component → Bool
  | .mem _ _ => true
  | _ => false

/-- Component `c` contains the memory byte at `x` (only `mem` components contain bytes). -/
def Component.Covers : Component → BitVec 64 → Prop
  | .mem addr len, x => ∃ i < len, x = addr + BitVec.ofNat 64 i
  | _, _ => False

/-- `s` and `s'` agree on component `c`. -/
def Component.Agrees (s s' : RamState) : Component → Prop
  | .reg r => s'.GPR[gprIndex r] = s.GPR[gprIndex r]
  | .flags => StatusFlags.ofRFLAGS s'.RFLAGS = StatusFlags.ofRFLAGS s.RFLAGS
  | .df => dfBit s'.RFLAGS = dfBit s.RFLAGS
  | .rip => s'.RIP = s.RIP
  | .mem addr len => ∀ i < len,
      s'.external[addr + BitVec.ofNat 64 i]? = s.external[addr + BitVec.ofNat 64 i]?
  | .xmm r => s'.ZMM[xmmIndex r].setWidth 128 = s.ZMM[xmmIndex r].setWidth 128
  | .mxcsr => s'.MXCSR = s.MXCSR
  | .fpr r => s'.FP87[fprIndex r] = s.FP87[fprIndex r]
  | .fsw => fswRest s'.FP87_Status = fswRest s.FP87_Status
  | .fcc => fswCC s'.FP87_Status = fswCC s.FP87_Status
  | .ftw => s'.FP87_Tag_Word = s.FP87_Tag_Word
  | .fcw => s'.FP87_Control = s.FP87_Control
  | .fpuPtr => fpuPtrOf s' = fpuPtrOf s

/-- Equal vector registers agree on every XMM component. -/
theorem Component.agrees_xmm_of_zmm {s s' : RamState} (h : s'.ZMM = s.ZMM) (r : BitVec 5) :
    (Component.xmm r).Agrees s s' := by
  simp only [Component.Agrees, h]

/-- Equal x87 register files agree on every x87 register component. -/
theorem Component.agrees_fpr_of_fp87 {s s' : RamState} (h : s'.FP87 = s.FP87) (r : BitVec 3) :
    (Component.fpr r).Agrees s s' := by
  simp only [Component.Agrees, h]

theorem Component.Agrees.refl (s : RamState) (c : Component) : c.Agrees s s := by
  cases c <;> simp [Component.Agrees]

theorem Component.Agrees.trans {s₁ s₂ s₃ : RamState} {c : Component}
    (h₁ : c.Agrees s₁ s₂) (h₂ : c.Agrees s₂ s₃) : c.Agrees s₁ s₃ := by
  cases c with
  | mem addr len => exact fun i hi => (h₂ i hi).trans (h₁ i hi)
  | _ => exact Eq.trans h₂ h₁

/-- Agreeing on a memory component means agreeing on every byte it covers. -/
theorem Component.Agrees.byte {s s' : RamState} {c : Component} (h : c.Agrees s s')
    {x : BitVec 64} (hx : c.Covers x) : s'.external[x]? = s.external[x]? := by
  cases c with
  | mem addr len => obtain ⟨i, hi, rfl⟩ := hx; exact h i hi
  | _ => exact hx.elim

/--
The part of `s` that `AgreesExcept` always keeps: `s` with the components an instruction may
write (general-purpose registers, the status flags, DF, RIP, memory, the XMM parts of the ZMM
registers, MXCSR, the x87 registers, status, tag and control words and last-instruction pointers)
and the per-step bookkeeping
(the oracle, `Next_IP`, the trace of memory accesses, and the fields `step` resets at its start,
`beforeFetch`) replaced by fixed values.
-/
def fixedPart (s : RamState) : RamState :=
  { beforeFetch s with
    GPR := Vector.replicate _ 0
    ZMM := s.ZMM.map xmmClear
    RFLAGS := clearDirectionFlag (clearStatusFlags s.RFLAGS)
    RIP := 0
    MXCSR := 0
    FP87 := Vector.replicate _ 0
    FP87_Status := 0
    FP87_Tag_Word := 0
    FP87_Control := 0
    FP87_FIP := 0
    FP87_FCS := 0
    FP87_FDP := 0
    FP87_FDS := 0
    FP87_FOP := 0
    Next_IP := 0
    oracle := {}
    external := ∅
    traceEventsRev := [] }

/--
`s'` agrees with `s` except possibly on the components in `cs` and on the per-step bookkeeping
(the oracle, `Next_IP`, the trace of memory accesses, and the fields `step` resets at its start).
Even when the status flags and DF are in `cs`, the other bits of RFLAGS agree.
-/
structure AgreesExcept (cs : List Component) (s s' : RamState) : Prop where
  /-- Every register-like component (general-purpose register, flags, DF, RIP, XMM register,
  MXCSR, x87 register, status, tag or control word, last-instruction pointers) outside `cs`
  agrees. -/
  agree : ∀ c, c ∉ cs → c.isMem = false → c.Agrees s s'
  /-- Every memory byte that no component of `cs` covers agrees. -/
  memory : ∀ x, (∀ c ∈ cs, ¬ c.Covers x) → s'.external[x]? = s.external[x]?
  /-- Everything else agrees. -/
  rest : fixedPart s' = fixedPart s
  /-- Memory only grows: a byte present in `s` is present in `s'` (a store inserts its bytes,
  nothing removes one). Written bytes keep being present, which a later access to them needs. -/
  grow : ∀ x : BitVec 64, (s.external[x]?).isSome → (s'.external[x]?).isSome

namespace AgreesExcept

variable {cs cs₁ cs₂ : List Component} {s s₁ s₂ s' : RamState}

theorem refl (cs : List Component) (s : RamState) : AgreesExcept cs s s :=
  ⟨fun c _ _ => Component.Agrees.refl s c, fun _ _ => rfl, rfl, fun _ h => h⟩

/-- Except `cs₁`, then except `cs₂`, is except `cs₁ ++ cs₂`. -/
theorem trans (h₁ : AgreesExcept cs₁ s s₁) (h₂ : AgreesExcept cs₂ s₁ s₂) :
    AgreesExcept (cs₁ ++ cs₂) s s₂ :=
  ⟨fun c hc hm => by
    simp only [List.mem_append, not_or] at hc
    exact (h₁.agree c hc.1 hm).trans (h₂.agree c hc.2 hm),
   fun x hx => (h₂.memory x fun c hc => hx c (List.mem_append_right _ hc)).trans
      (h₁.memory x fun c hc => hx c (List.mem_append_left _ hc)),
   h₂.rest.trans h₁.rest, fun x hx => h₂.grow x (h₁.grow x hx)⟩

/-- Components of `cs` that are not in `cs'` and agree anyway can be dropped. -/
theorem narrow {cs' : List Component} (h : AgreesExcept cs s s')
    (hc : ∀ c ∈ cs, c ∉ cs' → c.Agrees s s') : AgreesExcept cs' s s' := by
  classical
  refine ⟨fun c hc' hmem => if hm : c ∈ cs then hc c hm hc' else h.agree c hm hmem,
    fun x hx => ?_, h.rest, h.grow⟩
  by_cases hcov : ∃ c ∈ cs, c.Covers x
  · obtain ⟨c, hm, hcx⟩ := hcov
    exact (hc c hm fun hc' => hx c hc' hcx).byte hcx
  · exact h.memory x fun c hm hcx => hcov ⟨c, hm, hcx⟩

/-- A larger set of components. -/
theorem mono {cs' : List Component} (h : AgreesExcept cs s s') (hsub : ∀ c ∈ cs, c ∈ cs') :
    AgreesExcept cs' s s' :=
  h.narrow fun c hm hc' => absurd (hsub c hm) hc'

/-- Registers outside `cs` read the same, at any size. -/
theorem read {n : Nat} {r : BitVec 5} (h : AgreesExcept cs s s') (hr : .reg r ∉ cs) :
    (Operand.reg r : Operand n).read s' = (Operand.reg r : Operand n).read s := by
  have := h.agree _ hr rfl
  simp only [Component.Agrees] at this
  simp [Operand.read, this]

/-- AH–BH (bits 8–15 of a register outside `cs`) read the same. -/
theorem read_regHigh {n : Nat} {r : BitVec 5} (h : AgreesExcept cs s s') (hr : .reg r ∉ cs) :
    (Operand.regHigh r : Operand n).read s' = (Operand.regHigh r : Operand n).read s := by
  have := h.agree _ hr rfl
  simp only [Component.Agrees] at this
  simp [Operand.read, this]

/-- XMM registers outside `cs` read the same. -/
theorem read_xmm {r : BitVec 5} (h : AgreesExcept cs s s') (hr : .xmm r ∉ cs) :
    (Operand.xmm r : Operand 128).read s' = (Operand.xmm r : Operand 128).read s :=
  h.agree _ hr rfl

/-- A memory byte that no component of `cs` covers agrees. -/
theorem byte (h : AgreesExcept cs s s') {x : BitVec 64} (hx : ∀ c ∈ cs, ¬ c.Covers x) :
    s'.external[x]? = s.external[x]? :=
  h.memory x hx

/-- With no memory component in `cs`, all of memory agrees. -/
theorem external (h : AgreesExcept cs s s') (hcs : ∀ c ∈ cs, ∀ x, ¬ c.Covers x) :
    s'.external = s.external :=
  Std.ExtHashMap.ext_getElem? fun x => h.memory x fun c hc => hcs c hc x

theorem rip (h : AgreesExcept cs s s') (hr : .rip ∉ cs) : s'.RIP = s.RIP := h.agree _ hr rfl

/-- MXCSR outside `cs` is the same. -/
theorem mxcsr (h : AgreesExcept cs s s') (hm : .mxcsr ∉ cs) : s'.MXCSR = s.MXCSR :=
  h.agree _ hm rfl

/-- Physical x87 register R`r` outside `cs` is the same. -/
theorem fpr (h : AgreesExcept cs s s') {r : BitVec 3} (hr : .fpr r ∉ cs) :
    s'.FP87[fprIndex r] = s.FP87[fprIndex r] :=
  h.agree _ hr rfl

/-- The x87 status word outside `cs` is the same, except its condition codes. -/
theorem fsw (h : AgreesExcept cs s s') (hc : .fsw ∉ cs) :
    fswRest s'.FP87_Status = fswRest s.FP87_Status :=
  h.agree _ hc rfl

/-- The x87 condition codes outside `cs` are the same. -/
theorem fcc (h : AgreesExcept cs s s') (hc : .fcc ∉ cs) :
    fswCC s'.FP87_Status = fswCC s.FP87_Status :=
  h.agree _ hc rfl

/-- With neither the status word nor the condition codes in `cs`, all of the status word is the
same. -/
theorem fswAll (h : AgreesExcept cs s s') (hc : .fsw ∉ cs) (hcc : .fcc ∉ cs) :
    s'.FP87_Status = s.FP87_Status :=
  fsw_ext (h.fsw hc) (h.fcc hcc)

/-- The x87 tag word outside `cs` is the same. -/
theorem ftw (h : AgreesExcept cs s s') (hc : .ftw ∉ cs) : s'.FP87_Tag_Word = s.FP87_Tag_Word :=
  h.agree _ hc rfl

/-- The x87 control word outside `cs` is the same. -/
theorem fcw (h : AgreesExcept cs s s') (hc : .fcw ∉ cs) : s'.FP87_Control = s.FP87_Control :=
  h.agree _ hc rfl

/-- The x87 last-instruction pointers outside `cs` are the same. -/
theorem fpuPtr (h : AgreesExcept cs s s') (hc : .fpuPtr ∉ cs) : fpuPtrOf s' = fpuPtrOf s :=
  h.agree _ hc rfl

/-- The status flags outside `cs` are the same. -/
theorem statusFlags (h : AgreesExcept cs s s') (hf : .flags ∉ cs) :
    StatusFlags.ofRFLAGS s'.RFLAGS = StatusFlags.ofRFLAGS s.RFLAGS :=
  h.agree _ hf rfl

/-- The direction flag outside `cs` is the same. -/
theorem df (h : AgreesExcept cs s s') (hd : .df ∉ cs) : dfBit s'.RFLAGS = dfBit s.RFLAGS :=
  h.agree _ hd rfl

/-- With neither the status flags nor DF in `cs`, all of RFLAGS is the same. -/
theorem rflags (h : AgreesExcept cs s s') (hf : .flags ∉ cs) (hd : .df ∉ cs) :
    s'.RFLAGS = s.RFLAGS :=
  rflags_eq_of (congrArg (fun t => t.RFLAGS) h.rest) (h.statusFlags hf) (h.df hd)

end AgreesExcept

/-- Code that no memory component of `cs` covers stays in memory. -/
theorem CodeIn.of_agreesExcept {code : CodeMap} {cs : List Component} {s s' : RamState}
    (h : AgreesExcept cs s s') (hcode : ∀ x ∈ code, ∀ c ∈ cs, ¬ c.Covers x.1)
    (hin : CodeIn code s) : CodeIn code s' := fun x hx =>
  ⟨(hin x hx).1, (h.byte (hcode x hx)).trans (hin x hx).2⟩

/-- With no memory component in `cs`, all code stays in memory. -/
theorem AgreesExcept.codeIn {code : CodeMap} {cs : List Component} {s s' : RamState}
    (h : AgreesExcept cs s s') (hcs : ∀ c ∈ cs, ∀ x, ¬ c.Covers x) (hin : CodeIn code s) :
    CodeIn code s' :=
  hin.of_external_eq (h.external hcs)

/--
A step whose form ends in `writeOutputs` to register `r` changes only `r`, the status flags and RIP
(besides the per-step bookkeeping).
-/
theorem AgreesExcept.afterStep_writeOutputs (s : RamState) (length : Nat) {n : Nat} (r : BitVec 5)
    (out : RamState → BitVec n × StatusFlags) (oracleUsed : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.reg r, .flags, .rip] s
      (afterStep s length fun t => writeOutputs t (.reg r) (out t) oracleUsed nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r' =>
      have hne : r ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
      have := (Operand.read_afterStep s length
        (fun t => writeOutputs t (.reg r) (out t) oracleUsed nextIP) (.reg r' : Operand 64)).trans
        (Operand.read_writeOutputs_of_ne (m := 64) _ hne _ _ _)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => exact dfBit_store _ _
  · simp only [fixedPart, afterStep, finishStep, writeOutputs, Operand.write, setFlags, afterFetches,
      beforeFetch, resetStepFields, clearStatusFlags_store]

/--
A step whose form ends in `writeFlagsOutputs` changes only the status flags and RIP (besides the per-step
bookkeeping).
-/
theorem AgreesExcept.afterStep_writeFlagsOutputs (s : RamState) (length : Nat) (f : RamState → StatusFlags)
    (oracleUsed : Nat) (nextIP : BitVec 64) :
    AgreesExcept [.flags, .rip] s
      (afterStep s length fun t => writeFlagsOutputs t (f t) oracleUsed nextIP) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
    | flags => exact absurd (by simp) hc
    | rip => exact absurd (by simp) hc
    | mem addr len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => exact dfBit_store _ _
  · simp only [fixedPart, afterStep, finishStep, writeFlagsOutputs, setFlags, afterFetches, beforeFetch,
      resetStepFields, clearStatusFlags_store]

/-- Weakening: the registers (and flags, RIP) of `cs` are among those of `cs'`, and every byte a
memory component of `cs` covers is covered by one of `cs'`. -/
theorem AgreesExcept.widen {cs cs' : List Component} {s t : RamState} (h : AgreesExcept cs s t)
    (hreg : ∀ c ∈ cs, c.isMem = false → c ∈ cs')
    (hmem : ∀ x, ∀ c ∈ cs, c.Covers x → ∃ c' ∈ cs', c'.Covers x) : AgreesExcept cs' s t :=
  ⟨fun c hc hm => h.agree c (fun hin => hc (hreg c hin hm)) hm,
   fun x hx => h.memory x fun c hc hcov => by
     obtain ⟨c', hc', hcov'⟩ := hmem x c hc hcov
     exact hx c' hc' hcov',
   h.rest, h.grow⟩

end X86Proofs
