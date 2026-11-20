import X86Proofs.Program.ReadWrite.Sse
import X86Proofs.Program.ReadWrite.Float
import X86Proofs.Program.Compose

/-!
# MMX writes: an MMX register, the x87 status and tag words

Every MMX form (PADDB `mm, mm/m64`, MOVQ, PSLLW, …), after its checks (`CR0.EM = 0`, `CR0.TS = 0`,
no pending unmasked x87 exception), sets the x87 stack top TOP to 0 and the tag word to 0 (every
physical register valid): `mmxEnter t`. An MMX destination `r` is then written through
`Write_MMX`, which sets physical register R`r` to `0xFFFF ++ v` (`Operand.mmx r`, `mmxFpr`). The
forms end in `writeResult (mmxEnter t) (.mmx r) v nextIP` (register source) or
`writeResult (mmxEnter (dataAccess t "load")) (.mmx r) v nextIP` (memory source). After such a
step:

- `afterStep_mmx_rip`, `afterStep_load_mmx_rip`: RIP is `nextIP`;
- `Operand.read_afterStep_mmx_fpr`, `Operand.read_afterStep_load_mmx_fpr`,
  `Operand.read_afterStep_mmxEnter_fsw`, `Operand.read_afterStep_mmxEnter_ftw`: R`r` is
  `mmxFpr v`, the status word `mmxStatus` of the old one, the tag word 0;
- `AgreesExcept.afterStep_mmx`, `AgreesExcept.afterStep_load_mmx`: only R`r`, the status and tag
  words and RIP change;
- `ReadyToStep.afterStep_mmx`, `ReadyToStep.afterStep_load_mmx`: the state is ready to step again.

The building blocks: `AgreesExcept.write_fpr`, `AgreesExcept.write_mmx`, `AgreesExcept.write_fsw`,
`AgreesExcept.write_ftw`, `AgreesExcept.of_mmxEnter` (only the status and tag words change); EMMS
(which sets both words itself): `AgreesExcept.afterStep_fsw_ftw`, `afterStep_fsw_ftw_rip`.

Effects. `mmxEffect s nextIP r v`: R`r` := `mmxFpr v`, the status word := `mmxStatus` of the one
in `s`, the tag word := 0, RIP (`mmxEffect_holds`, `mmxEffect_holds_load`). A step whose
destination is not an MMX register (a store, a general-purpose or XMM register) has the effect of
that write plus the two words, `Effect.withMmx e s` (`Effect.Holds.withMmx`,
`Effect.Avoids.withMmx`, `ReadyToStep.of_mmxEnter`): `StepEffect.of_mmx_store_pre` (MOVQ `m64, mm`,
MOVNTQ), `mmxRegEffect_holds` (MOVD `r32, mm`, PMOVMSKB, PEXTRW), `mmxXmmEffect_holds` (MOVQ2DQ).
The conversions between MMX registers and SSE floats also write MXCSR: `mmxMxcsrEffect`
(`mmxMxcsrEffect_holds`, `…_load`: CVTPS2PI, …) and `xmmMxcsrMmxEffect_holds` (CVTPI2PS,
CVTPI2PD), with their frame lemmas `AgreesExcept.afterStep_mmx_mxcsr`, `…_load_mmx_mxcsr`.

Preconditions. `MmxPre p s`: RIP = `p`, `CR0.EM = CR0.TS = 0` (`Prelude.CR0.SSEEnabled`; with
`CR0.EM = 1` an MMX form raises #UD, with `CR0.TS = 1` #NM), FSW.ES clear (no pending unmasked x87
exception, which would raise #MF, `fswES`), and CPUID reports MMX (the opcode decoders check it
before they select an `NP 0F …` MMX form). `MmxSsePre` adds SSE (PMOVMSKB on an MMX register,
whose decoder checks SSE), `MmxSse2Pre` SSE2 (PADDQ, PSUBQ, PMULUDQ on MMX registers are SSE2
instructions; their decoders check both). `MmxLoadPre p addr len` adds that the `len` bytes at the
operand's address are readable (MMX memory operands use `Normal_Alignment`: no alignment
requirement), `MmxStorePre p codeLen addr len` that they are writable (`StorePre`). The forms that
are SSE forms as well (MOVQ2DQ, MOVDQ2Q, the conversions) take `MmxEnterPre pre`: an SSE
precondition `pre` and FSW.ES clear.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The x87 state an MMX instruction leaves besides its destination: TOP := 0 (`mmxStatus`) and
the tag word 0 (every physical register valid). -/
def mmxEnter (s : RamState) : RamState :=
  { s with FP87_Status := mmxStatus s.FP87_Status, FP87_Tag_Word := 0 }

/-- The precondition of an MMX triple at `p` with no memory operand: RIP = `p`, `CR0.EM` and
`CR0.TS` clear, no pending unmasked x87 exception (FSW.ES clear), and CPUID reports MMX. -/
structure MmxPre [Bindings] (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  cr0 : Prelude.CR0.SSEEnabled s.CR0
  es : fswES s.FP87_Status = 0
  mmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true

/-- `MmxPre`, and CPUID reports SSE2 (PADDQ, PSUBQ, PMULUDQ on MMX registers). -/
structure MmxSse2Pre [Bindings] (p : BitVec 64) (s : RamState) : Prop extends MmxPre p s where
  sse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true

/-- `MmxPre`, and CPUID reports SSE (PMOVMSKB on MMX registers, whose decoder checks SSE). -/
structure MmxSsePre [Bindings] (p : BitVec 64) (s : RamState) : Prop extends MmxPre p s where
  sse : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding true

/-- The precondition `pre` of an SSE form that also enters MMX mode (MOVQ2DQ, MOVDQ2Q, CVTPI2PS,
CVTPS2PI, …: `pre` is `Sse2Pre p`, `SseLoadNPre p addr 8`, …, whose decoders and forms check
SSE or SSE2 and `CR4.OSFXSR` as SSE forms do), and no pending unmasked x87 exception. -/
structure MmxEnterPre (pre : RamState → Prop) (s : RamState) : Prop where
  pre : pre s
  es : fswES s.FP87_Status = 0

/-- The precondition of an MMX load triple at `p` reading `len` bytes at `addr s`: `MmxPre` and
the bytes readable (no alignment requirement; they may cross a page). -/
structure MmxLoadPre [Bindings] (p : BitVec 64) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop extends MmxPre p s where
  read : MemReadable s (addr s) len

/-- `MmxLoadPre`, and CPUID reports SSE2. -/
structure MmxSse2LoadPre [Bindings] (p : BitVec 64) (addr : RamState → BitVec 64) (len : Nat)
    (s : RamState) : Prop extends MmxLoadPre p addr len s where
  sse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true

/-- The precondition of an MMX store triple at `p` for an instruction of `codeLen` bytes writing
the `len` bytes at `addr s`: `StorePre`, and the MMX conditions of `MmxPre`. -/
structure MmxStorePre [Bindings] (p : BitVec 64) (codeLen : Nat) (addr : RamState → BitVec 64)
    (len : Nat) (s : RamState) : Prop where
  store : StorePre p codeLen addr len s
  cr0 : Prelude.CR0.SSEEnabled s.CR0
  es : fswES s.FP87_Status = 0
  mmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true

@[simp] theorem afterFetches_FP87 (s : RamState) (k : Nat) : (afterFetches s k).FP87 = s.FP87 :=
  rfl

@[simp] theorem beforeFetch_FP87 (s : RamState) : (beforeFetch s).FP87 = s.FP87 := rfl

@[simp] theorem afterFetches_FP87_Status (s : RamState) (k : Nat) :
    (afterFetches s k).FP87_Status = s.FP87_Status := rfl

@[simp] theorem beforeFetch_FP87_Status (s : RamState) :
    (beforeFetch s).FP87_Status = s.FP87_Status := rfl

@[simp] theorem dataAccess_FP87_Status (s : RamState) (event : String) :
    (dataAccess s event).FP87_Status = s.FP87_Status := rfl

/-- How the MMX forms take a 64-bit source (`CheckedSlice.read (← Read_MMX r) 0 64`): the whole
value, the state unchanged. -/
theorem checkedSliceRead_mmx_run (x : BitVec 64) (s : RamState) :
    (X86.Runtime.CheckedSlice.read x 0 64 :
        X86.Runtime.SpecM X86.Exception RamState (X86.Runtime.Bits 64)).run s = (.ok x, s) := by
  rw [checkedSliceRead_eq_pure x (by decide) (by decide) (by decide)]
  simp only [Int.reduceToNat, BitVec.extractLsb'_eq_self]
  rfl

/-- `checkedSliceRead_mmx_run` in a form that may diverge (`PartialSpecM`: PSHUFW, PINSRW,
PEXTRW on MMX registers). -/
theorem checkedSliceRead_mmx_prun (x : BitVec 64) (s : RamState) :
    (X86.Runtime.CheckedSlice.read x 0 64 :
        X86.Runtime.PartialSpecM X86.Exception RamState (X86.Runtime.Bits 64)).run s =
      some (.ok x, s) := by
  rw [checkedSliceRead_eq_pure x (by decide) (by decide) (by decide)]
  simp only [Int.reduceToNat, BitVec.extractLsb'_eq_self]
  rfl

/-- An immediate byte sign-extended to 8 bits (`Std.Bits.Sign_Extend (source_size := 8) x 8`, how
the MMX shifts take their count) is the byte. -/
theorem signExtend8_run (x : BitVec 8) (s : RamState) :
    (X86.Helpers.Std.Bits.Sign_Extend (source_size := 8) x 8 :
        X86.Runtime.SpecM X86.Exception RamState (X86.Runtime.Bits 8)).run s = (.ok x, s) := by
  rw [stdSignExtend_eq_pure (n := 8) x (by decide) (by decide)]
  simp only [Int.reduceToNat, BitVec.signExtend_eq]
  rfl

/-! ### What the writes change -/

/-- An 80-bit write of physical x87 register R`r` changes only R`r`. -/
theorem AgreesExcept.write_fpr (t : RamState) (r : BitVec 3) (v : BitVec 80) :
    AgreesExcept [.fpr r] t ((Operand.fpr r : Operand 80).write t v) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | fpr r' =>
      have hne : r ≠ r' := fun h => hc (h ▸ List.mem_cons_self)
      have hi : (fprIndex r).val ≠ (fprIndex r').val := fun e =>
        hne (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, Operand.write_fpr, hi]
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · simp only [fixedPart, Operand.write_fpr, beforeFetch, resetStepFields]

/-- An MMX write of register `r` changes only physical register R`r`. -/
theorem AgreesExcept.write_mmx (t : RamState) (r : BitVec 3) (v : BitVec 64) :
    AgreesExcept [.fpr r] t ((Operand.mmx r : Operand 64).write t v) := by
  have := AgreesExcept.write_fpr t r (mmxFpr v)
  simpa only [Operand.write_fpr, Operand.write_mmx] using this

/-- Setting the x87 status word to a value with the same condition codes changes only the
status-word component. -/
theorem AgreesExcept.set_fsw (t : RamState) (v : BitVec 16)
    (hcc : fswCC v = fswCC t.FP87_Status) :
    AgreesExcept [.fsw] t { t with FP87_Status := v } := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | fsw => exact absurd List.mem_cons_self hc
    | fcc => exact hcc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · simp only [fixedPart, beforeFetch, resetStepFields]

/-- A write of the x87 status word (without its condition codes) changes only it. -/
theorem AgreesExcept.write_fsw (t : RamState) (v : BitVec 16) :
    AgreesExcept [.fsw] t ((Operand.fsw : Operand 16).write t v) := by
  rw [Operand.write_fsw]
  exact AgreesExcept.set_fsw t _ (fswCC_fswMerge _ _)

/-- A write of the x87 tag word changes only it. -/
theorem AgreesExcept.write_ftw (t : RamState) (v : BitVec 16) :
    AgreesExcept [.ftw] t ((Operand.ftw : Operand 16).write t v) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | ftw => exact absurd List.mem_cons_self hc
    | mem a len => exact fun _ _ => rfl
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | _ => rfl
  · simp only [fixedPart, Operand.write_ftw, beforeFetch, resetStepFields]

/-- Entering MMX mode (TOP := 0, every register tagged valid) changes only the status and tag
words. -/
theorem AgreesExcept.of_mmxEnter (t : RamState) : AgreesExcept [.fsw, .ftw] t (mmxEnter t) :=
  (AgreesExcept.set_fsw t (mmxStatus t.FP87_Status) (fswCC_mmxStatus _)).trans
    (AgreesExcept.write_ftw { t with FP87_Status := mmxStatus t.FP87_Status } 0)

/-- The components an MMX register write names, in the order the frame lemmas collect them. -/
theorem components_mmx (r : BitVec 3) :
    ∀ c ∈ ([] ++ [.fsw, .ftw] ++ [.fpr r] ++ [.rip] : List Component),
      c ∈ [.fpr r, .fsw, .ftw, .rip] := by
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hc ⊢
  rcases hc with h | h | h | h <;> simp [h]

/-! ### A step that writes an MMX register -/

/-- A step whose form ends in `writeResult (mmxEnter t) (.mmx r) v nextIP` changes only physical
register R`r`, the x87 status and tag words and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_mmx (s : RamState) (length : Nat) (r : BitVec 3)
    (v : RamState → BitVec 64) (nextIP : BitVec 64) :
    AgreesExcept [.fpr r, .fsw, .ftw, .rip] s
      (afterStep s length fun t => writeResult (mmxEnter t) (.mmx r) (v t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { t with Next_IP := nextIP }
  have h1 := AgreesExcept.prepare s (length + 1) nextIP
  have h2 := AgreesExcept.of_mmxEnter t0
  have h3 := AgreesExcept.write_mmx (mmxEnter t0) r (v t)
  have h4 := AgreesExcept.of_finishStep
    ((Operand.mmx r : Operand 64).write (mmxEnter t0) (v t))
  exact (((h1.trans h2).trans h3).trans h4).mono (components_mmx r)

/-- A load into MMX register `r` (`writeResult (mmxEnter (dataAccess t "load")) (.mmx r) v
nextIP`) changes only R`r`, the x87 status and tag words and RIP. -/
theorem AgreesExcept.afterStep_load_mmx (s : RamState) (length : Nat) (r : BitVec 3)
    (v : RamState → BitVec 64) (nextIP : BitVec 64) :
    AgreesExcept [.fpr r, .fsw, .ftw, .rip] s
      (afterStep s length fun t =>
        writeResult (mmxEnter (dataAccess t "load")) (.mmx r) (v t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { dataAccess t "load" with Next_IP := nextIP }
  have h1 : AgreesExcept [] s t0 := by
    refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | mem a l => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | _ => rfl
    · simp only [t0, t, fixedPart, dataAccess, afterFetches, beforeFetch, resetStepFields]
  have h2 := AgreesExcept.of_mmxEnter t0
  have h3 := AgreesExcept.write_mmx (mmxEnter t0) r (v t)
  have h4 := AgreesExcept.of_finishStep
    ((Operand.mmx r : Operand 64).write (mmxEnter t0) (v t))
  exact (((h1.trans h2).trans h3).trans h4).mono (components_mmx r)

/-- After a step whose form ends in `writeResult (mmxEnter t) (.mmx r) v nextIP`, RIP is
`nextIP`. -/
theorem afterStep_mmx_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 3) (v : RamState → BitVec 64) (nextIP : BitVec 64) :
    (afterStep s length fun t => writeResult (mmxEnter t) (.mmx r) (v t) nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeResult, mmxEnter, Operand.write, afterFetches, beforeFetch,
    resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After a load into an MMX register, RIP is `nextIP`. -/
theorem afterStep_load_mmx_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 3) (v : RamState → BitVec 64) (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      writeResult (mmxEnter (dataAccess t "load")) (.mmx r) (v t) nextIP).RIP = nextIP := by
  simp [afterStep, finishStep, writeResult, mmxEnter, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

/-- After an MMX write of register `r`, physical register R`r` is `0xFFFF ++ v`. -/
theorem Operand.read_afterStep_mmx_fpr (s : RamState) (length : Nat) (r : BitVec 3)
    (v : RamState → BitVec 64) (nextIP : BitVec 64) :
    (Operand.fpr r : Operand 80).read
        (afterStep s length fun t => writeResult (mmxEnter t) (.mmx r) (v t) nextIP) =
      mmxFpr (v (afterFetches (beforeFetch s) (length + 1))) := by
  rw [Operand.read_afterStep]
  simp [writeResult, mmxEnter, Operand.write, Operand.read]

/-- After a load into MMX register `r`, physical register R`r` is `0xFFFF ++ v`. -/
theorem Operand.read_afterStep_load_mmx_fpr (s : RamState) (length : Nat) (r : BitVec 3)
    (v : RamState → BitVec 64) (nextIP : BitVec 64) :
    (Operand.fpr r : Operand 80).read
        (afterStep s length fun t =>
          writeResult (mmxEnter (dataAccess t "load")) (.mmx r) (v t) nextIP) =
      mmxFpr (v (afterFetches (beforeFetch s) (length + 1))) := by
  rw [Operand.read_afterStep]
  simp [writeResult, mmxEnter, Operand.write, Operand.read]

/-- After an MMX instruction, the status word is the old one with TOP := 0. -/
theorem Operand.read_afterStep_mmxEnter_fsw (s : RamState) (length : Nat)
    (form : RamState → RamState) (hform : ∀ t, (form t).FP87_Status = mmxStatus t.FP87_Status) :
    (Operand.fsw : Operand 16).read (afterStep s length form) =
      mmxStatus ((Operand.fsw : Operand 16).read s) := by
  rw [Operand.read_afterStep]
  simp [hform, fswRest_mmxStatus]

/-- After an MMX instruction, the tag word is 0. -/
theorem Operand.read_afterStep_mmxEnter_ftw (s : RamState) (length : Nat)
    (form : RamState → RamState) (hform : ∀ t, (form t).FP87_Tag_Word = 0) :
    (Operand.ftw : Operand 16).read (afterStep s length form) = 0 := by
  rw [Operand.read_afterStep]
  simp [hform]

/-- Preservation for a form ending in `writeResult (mmxEnter t) (.mmx r) v nextIP`. -/
theorem ReadyToStep.afterStep_mmx [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 3) (v : RamState → BitVec 64) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t => writeResult (mmxEnter t) (.mmx r) (v t) nextIP) :=
  h.of_agreesExcept (AgreesExcept.afterStep_mmx s length r v nextIP) h.memory.tables

/-- Preservation for a load into an MMX register. -/
theorem ReadyToStep.afterStep_load_mmx [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 3) (v : RamState → BitVec 64) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (mmxEnter (dataAccess t "load")) (.mmx r) (v t) nextIP) :=
  h.of_agreesExcept (AgreesExcept.afterStep_load_mmx s length r v nextIP) h.memory.tables

/-- A step whose form sets `Next_IP` and the x87 status and tag words (EMMS), keeping the
condition codes, changes only those words and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_fsw_ftw (s : RamState) (length : Nat)
    (fsw ftw : RamState → BitVec 16) (nextIP : BitVec 64)
    (hcc : ∀ t, fswCC (fsw t) = fswCC t.FP87_Status) :
    AgreesExcept [.fsw, .ftw, .rip] s (afterStep s length fun t =>
      { t with
        Next_IP := nextIP
        FP87_Tag_Word := ftw t
        FP87_Status := fsw t }) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { t with Next_IP := nextIP }
  have h1 := AgreesExcept.prepare s (length + 1) nextIP
  have h2 := AgreesExcept.set_fsw t0 (fsw t) (hcc t)
  have h3 := AgreesExcept.write_ftw { t0 with FP87_Status := fsw t } (ftw t)
  have h4 := AgreesExcept.of_finishStep
    ((Operand.ftw : Operand 16).write { t0 with FP87_Status := fsw t } (ftw t))
  refine (((h1.trans h2).trans h3).trans h4).mono ?_
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hc ⊢
  rcases hc with h | h | h <;> simp [h]

/-- After a step that sets `Next_IP` and the x87 status and tag words, RIP is `nextIP`. -/
theorem afterStep_fsw_ftw_rip [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (fsw ftw : RamState → BitVec 16) (nextIP : BitVec 64) :
    (afterStep s length fun t =>
      { t with
        Next_IP := nextIP
        FP87_Tag_Word := ftw t
        FP87_Status := fsw t }).RIP = nextIP := by
  simp [afterStep, finishStep, afterFetches, beforeFetch, resetStepFields, h.ready.repeatClear,
    h.ready.msr]

/-! ### The effect of an MMX step -/

/-- The effect of a step to `nextIP` that writes MMX register `r` with `v`, from `s`: physical
register R`r` := `0xFFFF ++ v` (`mmxFpr`), TOP := 0 (`mmxStatus` of the status word in `s`), the
tag word := 0. -/
def mmxEffect (s : RamState) (nextIP : BitVec 64) (r : BitVec 3) (v : BitVec 64) : Effect :=
  { rip := nextIP
    writes := [⟨(Operand.fpr r : Operand 80), mmxFpr v⟩,
      ⟨(Operand.fsw : Operand 16), mmxStatus ((Operand.fsw : Operand 16).read s)⟩,
        ⟨(Operand.ftw : Operand 16), 0⟩] }

@[simp] theorem mmxEffect_components (s : RamState) (nextIP : BitVec 64) (r : BitVec 3)
    (v : BitVec 64) : (mmxEffect s nextIP r v).components = [.fpr r, .fsw, .ftw, .rip] := rfl

/-- A step whose form ends in `writeResult (mmxEnter t) (.mmx r) (v t) nextIP` has effect `e`,
any effect equal to `mmxEffect` with `v` at the state the form starts from. -/
theorem mmxEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 3) (v : RamState → BitVec 64) (nextIP : BitVec 64) {e : Effect}
    (he : e = mmxEffect s nextIP r (v (afterFetches (beforeFetch s) (length + 1)))) :
    e.Holds s (afterStep s length fun t => writeResult (mmxEnter t) (.mmx r) (v t) nextIP) :=
  he ▸ ⟨afterStep_mmx_rip h length r v nextIP,
    ⟨Operand.read_afterStep_mmx_fpr s length r v nextIP,
      Operand.read_afterStep_mmxEnter_fsw s length _ fun _ => rfl,
      Operand.read_afterStep_mmxEnter_ftw s length _ fun _ => rfl⟩,
    trivial, AgreesExcept.afterStep_mmx s length r v nextIP⟩

/-- A load into MMX register `r` has effect `mmxEffect` (as `mmxEffect_holds`). -/
theorem mmxEffect_holds_load [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 3) (v : RamState → BitVec 64) (nextIP : BitVec 64) {e : Effect}
    (he : e = mmxEffect s nextIP r (v (afterFetches (beforeFetch s) (length + 1)))) :
    e.Holds s (afterStep s length fun t =>
      writeResult (mmxEnter (dataAccess t "load")) (.mmx r) (v t) nextIP) :=
  he ▸ ⟨afterStep_load_mmx_rip h length r v nextIP,
    ⟨Operand.read_afterStep_load_mmx_fpr s length r v nextIP,
      Operand.read_afterStep_mmxEnter_fsw s length _ fun _ => rfl,
      Operand.read_afterStep_mmxEnter_ftw s length _ fun _ => rfl⟩,
    trivial, AgreesExcept.afterStep_load_mmx s length r v nextIP⟩

/-- Setting TOP to 0 twice is setting it once (two MMX instructions in a row). -/
@[x86_compose] theorem mmxStatus_mmxStatus (fsw : BitVec 16) :
    mmxStatus (mmxStatus fsw) = mmxStatus fsw := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mmxStatus]
  rw [getLsbD_setSlice _ _ _ _ _ hi, getLsbD_setSlice _ _ _ _ _ hi]
  split <;> rfl

attribute [x86_compose] mmxEffect

/-! ### Other MMX destinations: an effect, then `mmxEnter` -/

/-- Effect `e` of a step from `s`, plus what an MMX instruction does to the x87 state besides its
destination: TOP := 0 (the status word in `s` with `mmxStatus`) and the tag word := 0. -/
def Effect.withMmx (e : Effect) (s : RamState) : Effect :=
  { e with
    writes := e.writes ++
      [⟨(Operand.fsw : Operand 16), mmxStatus ((Operand.fsw : Operand 16).read s)⟩,
        ⟨(Operand.ftw : Operand 16), 0⟩] }

/-- `mmxEnter` changes no operand but the status and tag words. -/
theorem Operand.read_mmxEnter {n : Nat} (op : Operand n) (h1 : op.component ≠ .fsw)
    (h2 : op.component ≠ .ftw) (s : RamState) : op.read (mmxEnter s) = op.read s := by
  cases op <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2 |
    simp [Operand.read, mmxEnter, fswCC_mmxStatus]

theorem components_withMmx (e : Effect) (s : RamState) :
    ∀ c ∈ e.components ++ [.fsw, .ftw], c ∈ (e.withMmx s).components := by
  intro c hc
  simp only [Effect.withMmx, Effect.components, List.map_append, List.mem_append, List.map_cons,
    List.map_nil, List.mem_cons, List.mem_nil_iff, or_false, Write.component_fsw,
    Write.component_ftw] at hc ⊢
  rcases hc with ((h | h) | h) | h | h <;> simp [h]

/-- A step with effect `e` (which writes neither the status nor the tag word), followed by
`mmxEnter`, has effect `e.withMmx`. -/
theorem Effect.Holds.withMmx {e : Effect} {s s' : RamState} (h : e.Holds s s')
    (h1 : Component.fsw ∉ e.components) (h2 : Component.ftw ∉ e.components) :
    (e.withMmx s).Holds s (mmxEnter s') := by
  have hw := Write.allHold_iff.mp h.writes
  refine ⟨h.rip, Write.allHold_iff.mpr fun w hwm => ?_, h.flags,
    (h.agrees.trans (AgreesExcept.of_mmxEnter s')).mono (components_withMmx e s)⟩
  simp only [Effect.withMmx, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hwm
  rcases hwm with hwm | rfl | rfl
  · have hc : w.component ∈ e.components := Effect.mem_components.mpr (.inl ⟨w, hwm, rfl⟩)
    rw [Operand.read_mmxEnter w.dst (fun e => h1 (e ▸ hc)) (fun e => h2 (e ▸ hc))]
    exact hw w hwm
  · show fswRest (mmxStatus s'.FP87_Status) = mmxStatus (fswRest s.FP87_Status)
    rw [fswRest_mmxStatus, h.agrees.fsw h1]
  · rfl

/-- An effect plus the status and tag word writes avoids code if the effect does (those writes
cover no memory). -/
theorem Effect.Avoids.withMmx {e : Effect} {code : CodeMap} (h : e.Avoids code) (s : RamState) :
    (e.withMmx s).Avoids code := by
  intro x hx c hc hcov
  simp only [Effect.withMmx, Effect.components, List.map_append, List.mem_append, List.map_cons,
    List.map_nil, List.mem_cons, List.mem_nil_iff, or_false, Write.component_fsw,
    Write.component_ftw] at hc
  rcases hc with ((hc | hc | hc) | hc) | hc
  · exact h x hx c (by simp [Effect.components, hc]) hcov
  · subst hc; exact hcov
  · subst hc; exact hcov
  · exact h x hx c (by simp [Effect.components, hc]) hcov
  · exact h x hx c (by simp [Effect.components, hc]) hcov

/-- Preservation through `mmxEnter`: only the status and tag words change. -/
theorem ReadyToStep.of_mmxEnter [Bindings] {s : RamState} (h : ReadyToStep s) :
    ReadyToStep (mmxEnter s) :=
  h.of_agreesExcept (AgreesExcept.of_mmxEnter s) h.memory.tables

/-- The step of an MMX store form (MOVQ `m64, mm`, MOVNTQ, …) at `p` with its effect: the store
(`storeEffect`), TOP := 0 and the tag word := 0 (`Effect.withMmx`), under a precondition `P` that
implies `StorePre`, from its step theorem (as `StepEffect.of_store_pre`). -/
theorem StepEffect.of_mmx_store_pre [Bindings] {P : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {len : Nat} {n : Nat} (hn : n % 8 = 0) (h64 : n ≤ 128)
    (addr : RamState → BitVec 64) (v : RamState → BitVec n)
    (hpre : ∀ s, P s → StorePre p len addr (n / 8) s)
    (hstep : ∀ s, ReadyToStep s → CodeIn (codeRange p bytes) s → P s →
      X86.Machine.step s = some (.next (afterStep s len fun t =>
        writeResult (mmxEnter (dataAccess t "store")) (.mem (addr s) : Operand n) (v s)
          (BitVec.add p (BitVec.ofNat 64 len))))) :
    StepEffect P (codeRange p bytes) (fun s => (storeEffect p len addr v s).withMmx s) := by
  intro s h hcode hs
  have hp := hpre s hs
  have hst := hstep s h hcode hs
  have hready := ReadyToStep.afterStep_store h len (addr s) (v s)
    (BitVec.add p (BitVec.ofNat 64 len)) hp.write.low hp.write.tables
  have hholds : (storeEffect p len addr v s).Holds s (afterStep s len fun t =>
      writeResult (dataAccess t "store") (.mem (addr s) : Operand n) (v s)
        (BitVec.add p (BitVec.ofNat 64 len))) :=
    ⟨afterStep_store_rip h _ _ _ _, Operand.read_afterStep_store s _ hn h64 _ _ _, trivial,
      AgreesExcept.afterStep_store s _ _ _ _⟩
  exact ⟨_, hst, hready.of_mmxEnter, hholds.withMmx (by simp) (by simp)⟩

/-- A step whose form writes general-purpose register `r` (`n` bits: the 64-bit register becomes
`mergeGPR n v old`, which is `w`) and enters MMX mode, `writeResult (mmxEnter t) (.reg r) v
nextIP`, has effect `e`, the register write of `w` and RIP with `Effect.withMmx`. -/
theorem mmxRegEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 5) {n : Nat} (v : RamState → BitVec n) (nextIP : BitVec 64) {w : BitVec 64}
    (hw : mergeGPR n (v (afterFetches (beforeFetch s) (length + 1)))
      ((Operand.reg r : Operand 64).read s) = w) {e : Effect}
    (he : e = ({ rip := nextIP, writes := [⟨(Operand.reg r : Operand 64), w⟩] } :
      Effect).withMmx s) :
    e.Holds s (afterStep s length fun t => writeResult (mmxEnter t) (.reg r : Operand n) (v t)
      nextIP) := by
  subst he hw
  have hholds : ({ rip := nextIP
                   writes := [⟨(Operand.reg r : Operand 64), mergeGPR n
                     (v (afterFetches (beforeFetch s) (length + 1)))
                     ((Operand.reg r : Operand 64).read s)⟩] } : Effect).Holds s
      (afterStep s length fun t => writeResult t (.reg r : Operand n) (v t) nextIP) := by
    refine ⟨afterStep_writeResult_rip h _ _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s _ _ _ _⟩
    show Operand.read _ _ = _
    rw [Operand.read_afterStep, Operand.read_writeResult_self_merge]
    simp only [Operand.read_afterFetches, Operand.read_beforeFetch]
  exact hholds.withMmx (by simp [Effect.components]) (by simp [Effect.components])

/-- Preservation for a form ending in `writeResult (mmxEnter t) (.reg r) v nextIP`. -/
theorem ReadyToStep.afterStep_mmx_reg [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) {n : Nat} (r : BitVec 5) (v : RamState → BitVec n) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (mmxEnter t) (.reg r : Operand n) (v t) nextIP) :=
  (h.afterStep_writeResult length r v nextIP).of_mmxEnter

/-- A step whose form writes XMM register `r` and enters MMX mode (MOVQ2DQ), `writeResult
(mmxEnter t) (.xmm r) v nextIP`, has effect `e`, the XMM write and RIP with `Effect.withMmx`. -/
theorem mmxXmmEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 5) (v : RamState → BitVec 128) (nextIP : BitVec 64) {e : Effect}
    (he : e = ({ rip := nextIP, writes := [⟨(Operand.xmm r : Operand 128),
      v (afterFetches (beforeFetch s) (length + 1))⟩] } : Effect).withMmx s) :
    e.Holds s (afterStep s length fun t => writeResult (mmxEnter t) (.xmm r : Operand 128) (v t)
      nextIP) := by
  subst he
  have hholds : ({ rip := nextIP
                   writes := [⟨(Operand.xmm r : Operand 128),
                     v (afterFetches (beforeFetch s) (length + 1))⟩] } : Effect).Holds s
      (afterStep s length fun t => writeResult t (.xmm r : Operand 128) (v t) nextIP) :=
    ⟨afterStep_writeResult_rip h _ _ _ _, Operand.read_afterStep_writeResult_xmm s _ _ _ _,
      trivial, AgreesExcept.afterStep_writeResult_xmm s _ _ _ _⟩
  exact hholds.withMmx (by simp [Effect.components]) (by simp [Effect.components])

/-- Preservation for a form ending in `writeResult (mmxEnter t) (.xmm r) v nextIP`. -/
theorem ReadyToStep.afterStep_mmx_xmm [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 5) (v : RamState → BitVec 128) (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (mmxEnter t) (.xmm r : Operand 128) (v t) nextIP) :=
  (h.afterStep_writeResult_xmm length r v nextIP).of_mmxEnter

attribute [x86_compose] Effect.withMmx

/-! ### Conversions between MMX registers and SSE floats: MXCSR as well -/

/-- The components a conversion into MMX register `r` names, in the order the frame lemmas
collect them. -/
theorem components_fpr_mxcsr_rip (r : BitVec 3) :
    ∀ c ∈ ([] ++ [.mxcsr] ++ [.fpr r] ++ [.rip] : List Component),
      c ∈ [.fpr r, .mxcsr, .rip] := by
  intro c hc
  simp only [List.nil_append, List.cons_append, List.mem_cons, List.mem_nil_iff,
    or_false] at hc ⊢
  rcases hc with h | h | h <;> simp [h]

/-- A step whose form ends in `writeResult` to MMX register `r` after MXCSR is set to `m` (without
the x87 words, `mmxEnter`) changes only R`r`, MXCSR and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.afterStep_mmx_mxcsr (s : RamState) (length : Nat) (r : BitVec 3)
    (v : RamState → BitVec 64) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    AgreesExcept [.fpr r, .mxcsr, .rip] s
      (afterStep s length fun t =>
        writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.mmx r) (v t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { t with Next_IP := nextIP }
  have h1 := AgreesExcept.prepare s (length + 1) nextIP
  have h2 := AgreesExcept.write_mxcsr t0 (m t)
  have h3 := AgreesExcept.write_mmx ((Operand.mxcsr : Operand 32).write t0 (m t)) r (v t)
  have h4 := AgreesExcept.of_finishStep
    ((Operand.mmx r : Operand 64).write ((Operand.mxcsr : Operand 32).write t0 (m t)) (v t))
  exact (((h1.trans h2).trans h3).trans h4).mono (components_fpr_mxcsr_rip r)

/-- `AgreesExcept.afterStep_mmx_mxcsr` for a memory source (`dataAccess t "load"`). -/
theorem AgreesExcept.afterStep_load_mmx_mxcsr (s : RamState) (length : Nat) (r : BitVec 3)
    (v : RamState → BitVec 64) (m : RamState → BitVec 32) (nextIP : BitVec 64) :
    AgreesExcept [.fpr r, .mxcsr, .rip] s
      (afterStep s length fun t =>
        writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.mmx r)
          (v t) nextIP) := by
  let t := afterFetches (beforeFetch s) (length + 1)
  let t0 : RamState := { dataAccess t "load" with Next_IP := nextIP }
  have h1 : AgreesExcept [] s t0 := by
    refine ⟨fun c _ _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
    · cases c with
      | mem a l => exact fun _ _ => rfl
      | xmm x => exact Component.agrees_xmm_of_zmm rfl x
      | _ => rfl
    · simp only [t0, t, fixedPart, dataAccess, afterFetches, beforeFetch, resetStepFields]
  have h2 := AgreesExcept.write_mxcsr t0 (m t)
  have h3 := AgreesExcept.write_mmx ((Operand.mxcsr : Operand 32).write t0 (m t)) r (v t)
  have h4 := AgreesExcept.of_finishStep
    ((Operand.mmx r : Operand 64).write ((Operand.mxcsr : Operand 32).write t0 (m t)) (v t))
  exact (((h1.trans h2).trans h3).trans h4).mono (components_fpr_mxcsr_rip r)

/-- The effect of a step to `nextIP` that converts into MMX register `r` (CVTPS2PI, …): R`r` :=
`0xFFFF ++ v` (`mmxFpr`), MXCSR := `m`, and TOP := 0 and the tag word := 0 (`Effect.withMmx`). -/
def mmxMxcsrEffect (s : RamState) (nextIP : BitVec 64) (r : BitVec 3) (v : BitVec 64)
    (m : BitVec 32) : Effect :=
  ({ rip := nextIP
     writes := [⟨(Operand.fpr r : Operand 80), mmxFpr v⟩, ⟨(Operand.mxcsr : Operand 32), m⟩] } :
    Effect).withMmx s

@[simp] theorem mmxMxcsrEffect_components (s : RamState) (nextIP : BitVec 64) (r : BitVec 3)
    (v : BitVec 64) (m : BitVec 32) :
    (mmxMxcsrEffect s nextIP r v m).components = [.fpr r, .mxcsr, .fsw, .ftw, .rip] := rfl

/-- A step whose form converts into MMX register `r` and sets MXCSR, `writeResult (mmxEnter
(mxcsr.write t m)) (.mmx r) v nextIP`, has effect `mmxMxcsrEffect`. -/
theorem mmxMxcsrEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 3) (v : RamState → BitVec 64) (m : RamState → BitVec 32) (nextIP : BitVec 64)
    {e : Effect} (he : e = mmxMxcsrEffect s nextIP r (v (afterFetches (beforeFetch s) (length + 1)))
      (m (afterFetches (beforeFetch s) (length + 1)))) :
    e.Holds s (afterStep s length fun t =>
      writeResult (mmxEnter ((Operand.mxcsr : Operand 32).write t (m t))) (.mmx r) (v t)
        nextIP) := by
  subst he
  have hholds : ({ rip := nextIP
                   writes := [⟨(Operand.fpr r : Operand 80),
                       mmxFpr (v (afterFetches (beforeFetch s) (length + 1)))⟩,
                     ⟨(Operand.mxcsr : Operand 32),
                       m (afterFetches (beforeFetch s) (length + 1))⟩] } :
      Effect).Holds s (afterStep s length fun t =>
        writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.mmx r) (v t) nextIP) := by
    refine ⟨?_, ⟨?_, ?_⟩, trivial, AgreesExcept.afterStep_mmx_mxcsr s _ _ _ _ _⟩
    · simp [afterStep, finishStep, writeResult, Operand.write, afterFetches, beforeFetch,
        resetStepFields, h.ready.repeatClear, h.ready.msr]
    · rw [Operand.read_afterStep]
      simp [writeResult, Operand.write, Operand.read]
    · rfl
  exact hholds.withMmx (by simp [Effect.components]) (by simp [Effect.components])

/-- `mmxMxcsrEffect_holds` for a memory source. -/
theorem mmxMxcsrEffect_holds_load [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 3) (v : RamState → BitVec 64) (m : RamState → BitVec 32) (nextIP : BitVec 64)
    {e : Effect} (he : e = mmxMxcsrEffect s nextIP r (v (afterFetches (beforeFetch s) (length + 1)))
      (m (afterFetches (beforeFetch s) (length + 1)))) :
    e.Holds s (afterStep s length fun t =>
      writeResult (mmxEnter ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)))
        (.mmx r) (v t) nextIP) := by
  subst he
  have hholds : ({ rip := nextIP
                   writes := [⟨(Operand.fpr r : Operand 80),
                       mmxFpr (v (afterFetches (beforeFetch s) (length + 1)))⟩,
                     ⟨(Operand.mxcsr : Operand 32),
                       m (afterFetches (beforeFetch s) (length + 1))⟩] } :
      Effect).Holds s (afterStep s length fun t =>
        writeResult ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)) (.mmx r)
          (v t) nextIP) := by
    refine ⟨?_, ⟨?_, ?_⟩, trivial, AgreesExcept.afterStep_load_mmx_mxcsr s _ _ _ _ _⟩
    · simp [afterStep, finishStep, writeResult, Operand.write, dataAccess, afterFetches,
        beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]
    · rw [Operand.read_afterStep]
      simp [writeResult, Operand.write, Operand.read]
    · rfl
  exact hholds.withMmx (by simp [Effect.components]) (by simp [Effect.components])

/-- Preservation for a conversion into an MMX register. -/
theorem ReadyToStep.afterStep_mmx_mxcsr [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 3) (v : RamState → BitVec 64) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (mmxEnter ((Operand.mxcsr : Operand 32).write t (m t))) (.mmx r) (v t)
        nextIP) :=
  (h.of_agreesExcept (AgreesExcept.afterStep_mmx_mxcsr s length r v m nextIP)
    h.memory.tables).of_mmxEnter

/-- Preservation for a conversion into an MMX register from memory. -/
theorem ReadyToStep.afterStep_load_mmx_mxcsr [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 3) (v : RamState → BitVec 64) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (mmxEnter ((Operand.mxcsr : Operand 32).write (dataAccess t "load") (m t)))
        (.mmx r) (v t) nextIP) :=
  (h.of_agreesExcept (AgreesExcept.afterStep_load_mmx_mxcsr s length r v m nextIP)
    h.memory.tables).of_mmxEnter

/-- A step whose form converts an MMX register into XMM register `r` and sets MXCSR (CVTPI2PS,
CVTPI2PD), `writeResult (mmxEnter (mxcsr.write t m)) (.xmm r) v nextIP`, has effect `e`: the XMM
and MXCSR writes and RIP with `Effect.withMmx`. -/
theorem xmmMxcsrMmxEffect_holds [Bindings] {s : RamState} (h : ReadyToStep s) (length : Nat)
    (r : BitVec 5) (v : RamState → BitVec 128) (m : RamState → BitVec 32) (nextIP : BitVec 64)
    {e : Effect}
    (he : e = ({ rip := nextIP
                 writes := [⟨(Operand.xmm r : Operand 128),
                     v (afterFetches (beforeFetch s) (length + 1))⟩,
                   ⟨(Operand.mxcsr : Operand 32),
                     m (afterFetches (beforeFetch s) (length + 1))⟩] } :
      Effect).withMmx s) :
    e.Holds s (afterStep s length fun t =>
      writeResult (mmxEnter ((Operand.mxcsr : Operand 32).write t (m t))) (.xmm r) (v t)
        nextIP) := by
  subst he
  have hholds : ({ rip := nextIP
                   writes := [⟨(Operand.xmm r : Operand 128),
                       v (afterFetches (beforeFetch s) (length + 1))⟩,
                     ⟨(Operand.mxcsr : Operand 32),
                       m (afterFetches (beforeFetch s) (length + 1))⟩] } :
      Effect).Holds s (afterStep s length fun t =>
        writeResult ((Operand.mxcsr : Operand 32).write t (m t)) (.xmm r) (v t) nextIP) :=
    ⟨afterStep_writeResult_xmm_mxcsr_rip h _ _ _ _ _,
      ⟨Operand.read_afterStep_writeResult_xmm_mxcsr s _ _ _ _ _,
        Operand.read_afterStep_writeResult_mxcsr s _ _ _ _ _⟩, trivial,
      AgreesExcept.afterStep_writeResult_xmm_mxcsr s _ _ _ _ _⟩
  exact hholds.withMmx (by simp [Effect.components]) (by simp [Effect.components])

/-- Preservation for a conversion from an MMX register into an XMM register. -/
theorem ReadyToStep.afterStep_xmm_mxcsr_mmx [Bindings] {s : RamState} (h : ReadyToStep s)
    (length : Nat) (r : BitVec 5) (v : RamState → BitVec 128) (m : RamState → BitVec 32)
    (nextIP : BitVec 64) :
    ReadyToStep (afterStep s length fun t =>
      writeResult (mmxEnter ((Operand.mxcsr : Operand 32).write t (m t))) (.xmm r) (v t)
        nextIP) :=
  (h.afterStep_writeResult_xmm_mxcsr length r v m nextIP).of_mmxEnter

attribute [x86_compose] mmxMxcsrEffect

/-! ### Preconditions after an effect -/

/-- `CR0.EM` and `CR0.TS` stay clear across any effect (`fixedPart` keeps CR0). -/
theorem MmxPre.cr0_of_holds {e : Effect} {s s' : RamState} (h : e.Holds s s')
    (hc : Prelude.CR0.SSEEnabled s.CR0) : Prelude.CR0.SSEEnabled s'.CR0 :=
  (SameControls.of_fixedPart h.agrees.rest).cr0 ▸ hc

/-- A CPUID feature (MMX, …) stays reported across any effect. -/
theorem MmxPre.mmx_of_holds [Bindings] {e : Effect} {s s' : RamState} (h : e.Holds s s')
    (hs : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true) :
    Prelude.ReportsCPUFeature Bindings.processor s' CPUID_MMX_Encoding true :=
  reportsCPUFeature_of_sameControls (SameControls.of_fixedPart h.agrees.rest) hs

/-! ### More preconditions after an effect -/

section Carry

variable {e : Effect} {s s' : RamState}

theorem fswES_of_obs (ho : Obs (e.after s true) s')
    (hes : fswES ((Operand.fsw : Operand 16).read (e.after s true)) = 0) :
    fswES s'.FP87_Status = 0 := by
  rw [← fswES_fswRest, ← ho.fsw]
  simpa [Operand.read] using hes

@[x86_pre] theorem MmxPre.of_holds [Bindings] (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p : BitVec 64} (hrip : e.rip = p) (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES ((Operand.fsw : Operand 16).read (e.after s true)) = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true) :
    MmxPre p s' :=
  ⟨h.rip_of hrip, h.CR0_eq ▸ hcr0, fswES_of_obs ho hes, h.reportsCPUFeature_iff.mpr hmmx⟩

@[x86_pre] theorem MmxSse2Pre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} (hrip : e.rip = p)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES ((Operand.fsw : Operand 16).read (e.after s true)) = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true) :
    MmxSse2Pre p s' :=
  ⟨MmxPre.of_holds h ho hrip hcr0 hes hmmx, h.reportsCPUFeature_iff.mpr hsse2⟩

@[x86_pre] theorem MmxSsePre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} (hrip : e.rip = p)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES ((Operand.fsw : Operand 16).read (e.after s true)) = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (hsse : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE_Encoding true) :
    MmxSsePre p s' :=
  ⟨MmxPre.of_holds h ho hrip hcr0 hes hmmx, h.reportsCPUFeature_iff.mpr hsse⟩

@[x86_pre] theorem MmxEnterPre.of_holds (ho : Obs (e.after s true) s') {pre : RamState → Prop}
    (hpre : pre s') (hes : fswES ((Operand.fsw : Operand 16).read (e.after s true)) = 0) :
    MmxEnterPre pre s' :=
  ⟨hpre, fswES_of_obs ho hes⟩

@[x86_pre] theorem MmxLoadPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {addr : RamState → BitVec 64} {len : Nat}
    (hrip : e.rip = p) (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES ((Operand.fsw : Operand 16).read (e.after s true)) = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (ha : AddrObs addr) (hr : MemReadable s (addr (e.after s true)) len) :
    MmxLoadPre p addr len s' :=
  ⟨MmxPre.of_holds h ho hrip hcr0 hes hmmx, MemReadable.carry h ho ha hr⟩

@[x86_pre] theorem MmxSse2LoadPre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {addr : RamState → BitVec 64} {len : Nat}
    (hrip : e.rip = p) (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES ((Operand.fsw : Operand 16).read (e.after s true)) = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (hsse2 : Prelude.ReportsCPUFeature Bindings.processor s CPUID_SSE2_Encoding true)
    (ha : AddrObs addr) (hr : MemReadable s (addr (e.after s true)) len) :
    MmxSse2LoadPre p addr len s' :=
  ⟨MmxLoadPre.of_holds h ho hrip hcr0 hes hmmx ha hr, h.reportsCPUFeature_iff.mpr hsse2⟩

@[x86_pre] theorem MmxStorePre.of_holds [Bindings] (h : e.Holds s s')
    (ho : Obs (e.after s true) s') {p : BitVec 64} {codeLen : Nat}
    {addr : RamState → BitVec 64} {len : Nat} (hrip : e.rip = p)
    (hcr0 : Prelude.CR0.SSEEnabled s.CR0)
    (hes : fswES ((Operand.fsw : Operand 16).read (e.after s true)) = 0)
    (hmmx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_MMX_Encoding true)
    (ha : AddrObs addr) (hw : MemWritable s (addr (e.after s true)) len)
    (hap : RangeApart (addr (e.after s true)) len p codeLen) :
    MmxStorePre p codeLen addr len s' :=
  ⟨StorePre.of_holds h ho hrip ha hw hap, h.CR0_eq ▸ hcr0, fswES_of_obs ho hes,
    h.reportsCPUFeature_iff.mpr hmmx⟩

end Carry

end X86Proofs
