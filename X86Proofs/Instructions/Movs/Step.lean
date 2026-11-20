import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Program.Agrees
import X86Proofs.Instructions.Movs.Decode
import X86Proofs.Instructions.Movs.Form

/-!
# Layer 3: `movsb` step theorem and preservation
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The state `movsb` (one byte, `A4` at RIP) steps to: `afterStep` around `movsSpec 8`. -/
def movsbAfter (s : RamState) : RamState :=
  afterStep s 1 fun t => movsSpec 8 { t with Next_IP := BitVec.add s.RIP 1#64 }

/--
Layer 3 for `movsb` (`A4`, no prefix). If the machine is ready to step, the direction flag is
clear, the byte `A4` is at RIP below 4 GiB, and the bytes at RSI and RDI lie below 4 GiB and are
present in RAM, one `step` runs normally: it copies the byte at RSI to RDI, advances RSI and RDI
by one, sets `Next_IP` = RIP + 1 and does the per-step housekeeping (`movsbAfter`).
-/
theorem movsb_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hdf : DirectionFlagClear s.RFLAGS)
    (hcode : BytesAt s s.RIP [0xA4]) (hlow : s.RIP.toNat + 1 ≤ 2^32)
    (hsrc : (rsi.read s).toNat + 1 ≤ 2^32) (hdst : (rdi.read s).toNat + 1 ≤ 2^32)
    (hsrcMem : (s.external[rsi.read s]?).isSome) (hdstMem : (s.external[rdi.read s]?).isSome) :
    X86.Machine.step s = some (.next (movsbAfter s)) := by
  have hdecode := decodeLegacy0_run_of_A4 s h hcode hlow
  let t := afterFetches (beforeFetch s) 2
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  rw [movsb_form t _ _ ht hmode rfl rfl rfl rfl rfl rfl h.cpu.ds h.cpu.es hdf hsrc hdst hsrcMem
    hdstMem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  · exact step_none_legacy0 s _ h 0xA4 [] (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode
      hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

@[simp] theorem movsbAfter_rip [Bindings] {s : RamState} (h : ReadyToStep s) :
    (movsbAfter s).RIP = BitVec.add s.RIP 1#64 := by
  simp [movsbAfter, afterStep, finishStep, movsSpec, Operand.write, dataAccess, afterFetches,
    beforeFetch, resetStepFields, h.ready.repeatClear, h.ready.msr]

theorem movsbAfter_external (s : RamState) :
    (movsbAfter s).external =
      memStore s.external (rdi.read s) ((Operand.mem (rsi.read s) : Operand 8).read s) := rfl

theorem movsbAfter_gpr (s : RamState) :
    (movsbAfter s).GPR = Vector.set (Vector.set s.GPR 6 (s.GPR[6] + 1)) 7 (s.GPR[7] + 1) := by
  simp [movsbAfter, afterStep, finishStep, movsSpec, Operand.write, Operand.read, dataAccess,
    afterFetches, beforeFetch, resetStepFields, gprIndex, mergeGPR_64]
  rfl

theorem movsbAfter_rsi (s : RamState) : rsi.read (movsbAfter s) = rsi.read s + 1 := by
  simp [Operand.read, movsbAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem movsbAfter_rdi (s : RamState) : rdi.read (movsbAfter s) = rdi.read s + 1 := by
  simp [Operand.read, movsbAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

/-- The byte at the old RDI after `movsb` is the byte that was at the old RSI. -/
theorem movsbAfter_copy (s : RamState) :
    (Operand.mem (rdi.read s) : Operand 8).read (movsbAfter s) =
      (Operand.mem (rsi.read s) : Operand 8).read s := by
  simp only [Operand.read]
  rw [movsbAfter_external]
  exact memLoad_memStore_8 _ _ _

/--
Preservation for `movsb_step`: if the byte written (at RDI) lies below 4 GiB and outside the
page-table frames, the state after the step is ready to step again. RFLAGS, the control and
segment registers and `Repeat_String_Operation` are untouched (`MOVSB` without REP never sets
it), and the page tables survive the write.
-/
theorem movsb_ready [Bindings] {s : RamState} (h : ReadyToStep s)
    (hdst : (rdi.read s).toNat + 1 ≤ 2^32)
    (htables : PageTableEntriesApart (rdi.read s).toNat 1) :
    ReadyToStep (movsbAfter s) := by
  have hst : SameControls s (movsbAfter s) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc := h.cpu
  have hr := h.ready
  have hmem : Prelude.IdentityMappedMemory (movsbAfter s) := by
    refine ⟨h.memory.cr3, ?_⟩
    rw [movsbAfter_external]
    exact IdentityPageTableMemory.memStore h.memory.tables _ _ hdst htables
  exact ⟨⟨hc.cs, hc.ss, hc.ds, hc.es, hc.cpl, hc.cr0, hc.cr4, hc.efer, hc.maxPhysical, hc.early,
      reportsCPUFeature_of_sameControls hst hc.lam, reportsCPUFeature_of_sameControls hst hc.lass, hc.debug,
      hc.aet⟩,
    hmem,
    ⟨hr.event, hr.active, hr.sti, hr.movss, hr.singleStep, hr.taskSwitch, hr.breakpoint,
      hr.busLock, hr.tf, hr.rf, hr.repeatClear, hr.msr⟩,
    smrrUnblocked_of_sameControls hst h.smrr, writeBackMemoryType_of_sameControls hst h.memoryType,
    h.features.of_sameControls hst⟩

/-- `movsb` changes only RSI, RDI, the byte at RDI and RIP (besides the per-step bookkeeping). -/
theorem AgreesExcept.movsb (s : RamState) :
    AgreesExcept [.reg 6, .reg 7, .mem (rdi.read s) 1, .rip] s (movsbAfter s) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h6 : r ≠ 6 := fun h => hc (by simp [h])
      have h7 : r ≠ 7 := fun h => hc (by simp [h])
      have h6' : r.toNat ≠ 6 := fun e => h6 (BitVec.eq_of_toNat_eq e)
      have h7' : r.toNat ≠ 7 := fun e => h7 (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, movsbAfter_gpr, gprIndex, Ne.symm h6', Ne.symm h7']
    | flags => rfl
    | rip => exact absurd (by simp) hc
    | mem a len => exact absurd hm (by simp [Component.isMem])
    | xmm x => exact Component.agrees_xmm_of_zmm rfl x
    | mxcsr => rfl
    | fpr x => exact Component.agrees_fpr_of_fp87 rfl x
    | fsw => rfl
    | fcc => rfl
    | ftw => rfl
    | fcw => rfl
    | fpuPtr => rfl
    | df => rfl
  · rw [movsbAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) 1) (by simp) ⟨i, by omega, he.symm⟩
  · simp only [fixedPart, X86Proofs.movsbAfter, afterStep, finishStep, movsSpec, Operand.write,
      dataAccess, afterFetches, beforeFetch, resetStepFields]
  · rw [movsbAfter_external]
    exact memStore_isSome _ _ _ x hx

end X86Proofs
