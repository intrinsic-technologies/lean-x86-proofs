import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Program.Agrees
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Instructions.Movs.Decode
import X86Proofs.Instructions.Movs.RepForm

/-!
# Layer 3: one `rep movsq` step

One `step` of `F3 REX.W A5` with RCX ≠ 0 copies one quadword and decrements RCX
(`rep_movsq_step`, ending in `repMovsqAfter`); RIP moves on only when RCX reaches 0. With RCX = 0
the step copies nothing and moves RIP on (`rep_movsq_step_zero`, ending in `repMovsqZeroAfter`).

Both take `ReadyMidRep` (`ReadyToStep` up to the repeat flag), since the iterations after the first
start with the flag set. The frame facts are stated between the states with the flag cleared
(`clearRep`): `AgreesExcept` compares the flag, which an iteration changes, so with the flag
cleared the per-iteration `AgreesExcept` facts chain with `AgreesExcept.trans`; at the end of the
instruction the flag is clear again (`AgreesExcept.of_clearRep`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The state one `rep movsq` step with RCX ≠ 0 ends in: `afterStep` around one quadword move and
`repCount`, with `Next_IP` = RIP + 3. -/
def repMovsqAfter (s : RamState) : RamState :=
  afterStep s 3 fun t => repCount (movsSpec 64 { t with Next_IP := BitVec.add s.RIP 3#64 })

/-- The state one `rep movsq` step with RCX = 0 ends in. -/
def repMovsqZeroAfter (s : RamState) : RamState :=
  afterStep s 3 fun t =>
    { t with Next_IP := BitVec.add s.RIP 3#64, Repeat_String_Operation := false }

/--
Layer 3 for `rep movsq` (`F3 rex A5`, REX.W) with RCX ≠ 0. If the machine is ready to step up to
the repeat flag, the direction flag is clear, the stride binding answers 1, the bytes are at RIP
below 4 GiB, and the 8 bytes at RSI and the 8 bytes at RDI lie below 4 GiB and are present in RAM,
one `step` copies the quadword at RSI to RDI, advances RSI and RDI by 8 and decrements RCX
(`repMovsqAfter`).
-/
theorem rep_movsq_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (rex : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP [0xF3, rex, 0xA5])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hsrc : (rsi.read s).toNat + 8 ≤ 2^32) (hdst : (rdi.read s).toNat + 8 ≤ 2^32)
    (hsrcMem : ∀ i, i < 8 → (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome)
    (hdstMem : ∀ i, i < 8 → (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) :
    X86.Machine.step s = some (.next (repMovsqAfter s)) := by
  have hdecode := decodeLegacy0_run_of_F3_rex_A5 s h rex hrex hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 4
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsq_form hstride t _ _ ht hmode rfl rfl rfl (repRexContext_rex_w hrex _) rfl rfl
    hcpu.ds hcpu.es hdf hcount hsrc hdst hsrcMem hdstMem] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (repRexContext s.DS rex.toBitVec) = true := rfl
  have hstep := step_f3_rex_legacy0 s _ h rex 0xA5 [] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

/-- Layer 3 for `rep movsq` with RCX = 0: one `step` copies nothing and moves RIP on
(`repMovsqZeroAfter`). -/
theorem rep_movsq_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hcode : BytesAt s s.RIP [0xF3, rex, 0xA5])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repMovsqZeroAfter s)) := by
  have hdecode := decodeLegacy0_run_of_F3_rex_A5 s h rex hrex hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 4
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  rw [rep_movsq_form_zero t _ _ rfl rfl rfl (repRexContext_rex_w hrex _) hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (repRexContext s.DS rex.toBitVec) = true := rfl
  have hstep := step_f3_rex_legacy0 s _ h rex 0xA5 [] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

/-! ### After an iteration -/

theorem repMovsqAfter_external (s : RamState) :
    (repMovsqAfter s).external =
      memStore s.external (rdi.read s) ((Operand.mem (rsi.read s) : Operand 64).read s) := rfl

@[simp] theorem repMovsqAfter_rflags (s : RamState) : (repMovsqAfter s).RFLAGS = s.RFLAGS := rfl

theorem repMovsqAfter_gpr (s : RamState) :
    (repMovsqAfter s).GPR = Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] + 8)) 7
      (s.GPR[7] + 8)) 1 (s.GPR[1] - 1) := by
  simp [repMovsqAfter, repCount, afterStep, finishStep, movsSpec, Operand.write, Operand.read,
    dataAccess, afterFetches, beforeFetch, resetStepFields, gprIndex, mergeGPR_64, Vector.getElem_set]
  rfl

theorem repMovsqAfter_rsi (s : RamState) : rsi.read (repMovsqAfter s) = rsi.read s + 8 := by
  simp [Operand.read, repMovsqAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repMovsqAfter_rdi (s : RamState) : rdi.read (repMovsqAfter s) = rdi.read s + 8 := by
  simp [Operand.read, repMovsqAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repMovsqAfter_rcx (s : RamState) : rcx.read (repMovsqAfter s) = rcx.read s - 1 := by
  simp [Operand.read, repMovsqAfter_gpr, gprIndex]

theorem rcx_read_movsSpec (n : Nat) (t : RamState) : rcx.read (movsSpec n t) = rcx.read t := by
  simp only [movsSpec]
  rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_reg_write_mem, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]

theorem repMovsqAfter_repeat (s : RamState) :
    (repMovsqAfter s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  simp only [repMovsqAfter, afterStep, finishStep, repCount, rcx_read_movsSpec]
  rfl

theorem repMovsqAfter_rip (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repMovsqAfter s).RIP = if rcx.read s - 1 = 0 then BitVec.add s.RIP 3#64 else s.RIP := by
  simp only [repMovsqAfter, afterStep, finishStep, repCount, rcx_read_movsSpec]
  simp [movsSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

/-- One iteration changes only RCX, RSI, RDI, the 8 bytes at RDI and RIP (besides the
bookkeeping and the repeat flag). -/
theorem AgreesExcept.repMovsq (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) 8, .rip] (clearRep s)
      (clearRep (repMovsqAfter s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repMovsqAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6,
        Ne.symm h7]
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
  · simp only [clearRep_external]
    rw [repMovsqAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) 8) (by simp) ⟨i, by omega, he.symm⟩
  · simp only [fixedPart, clearRep, repMovsqAfter, repCount, afterStep, finishStep, movsSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · simp only [clearRep_external] at hx ⊢
    rw [repMovsqAfter_external]
    exact memStore_isSome _ _ _ x hx

/-- Preservation: if the 8 bytes written lie below 4 GiB and outside the page-table frames, the
state after an iteration is ready to step up to the repeat flag. -/
theorem ReadyMidRep.repMovsq [Bindings] {s : RamState} (h : ReadyMidRep s)
    (hdst : (rdi.read s).toNat + 8 ≤ 2^32)
    (htables : PageTableEntriesApart (rdi.read s).toNat 8) :
    ReadyMidRep (repMovsqAfter s) := by
  have htab : IdentityPageTableMemory (clearRep (repMovsqAfter s)).external := by
    rw [clearRep_external, repMovsqAfter_external]
    exact IdentityPageTableMemory.memStore (ReadyToStep.memory (s := clearRep s) h).tables _ _
      (by omega) (by omega)
  have : ReadyToStep (clearRep (repMovsqAfter s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repMovsq s) htab
  exact this

/-- After an iteration, the destination byte `i` (`i < 8`) holds the source byte `i`, if that is
present. -/
theorem repMovsqAfter_copy (s : RamState) (i : Nat) (hi : i < 8)
    (hsrc : (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome) :
    (repMovsqAfter s).external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  rw [repMovsqAfter_external, memStore_getElem?_self _ _ _ (by decide) i (by omega)]
  simp only [Operand.read]
  rw [storedByte_memLoad _ _ i (by omega), memByte]
  simp only [PhysicalMemory.read]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsrc
  change some ((s.external[rsi.read s + BitVec.ofNat 64 i]?).getD 0) =
    s.external[rsi.read s + BitVec.ofNat 64 i]?
  rw [hb]
  rfl

/-! ### After the RCX = 0 step -/

@[simp] theorem repMovsqZeroAfter_external (s : RamState) :
    (repMovsqZeroAfter s).external = s.external := rfl

theorem repMovsqZeroAfter_rip (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repMovsqZeroAfter s).RIP = BitVec.add s.RIP 3#64 := by
  simp [repMovsqZeroAfter, afterStep, finishStep, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem repMovsqZeroAfter_repeat (s : RamState) :
    (repMovsqZeroAfter s).Repeat_String_Operation = false := rfl

theorem AgreesExcept.repMovsqZero (s : RamState) :
    AgreesExcept [.rip] (clearRep s) (clearRep (repMovsqZeroAfter s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r => rfl
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
  · simp only [fixedPart, clearRep, repMovsqZeroAfter, afterStep, finishStep, afterFetches,
      beforeFetch, resetStepFields]

end X86Proofs
