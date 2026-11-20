
import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.RepString
import X86Proofs.Instructions.Movs.RepStep
import X86Proofs.Instructions.Movs.Generated.Rep.Decode
import X86Proofs.Instructions.Movs.Generated.Rep.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

def repMovsAfter (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repCount (movsSpec n { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len) })

theorem repMovsAfter_external (n len : Nat) (s : RamState) :
    (repMovsAfter n len s).external =
      memStore s.external (rdi.read s) ((Operand.mem (rsi.read s) : Operand n).read s) := rfl

@[simp] theorem repMovsAfter_rflags (n len : Nat) (s : RamState) :
    (repMovsAfter n len s).RFLAGS = s.RFLAGS := rfl

theorem repMovsAfter_gpr (n len : Nat) (s : RamState) :
    (repMovsAfter n len s).GPR =
      Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (s.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (s.GPR[1] - 1) := by
  simp [repMovsAfter, repCount, afterStep, finishStep, movsSpec, Operand.write, Operand.read,
    dataAccess, afterFetches, beforeFetch, resetStepFields, gprIndex, mergeGPR_64, Vector.getElem_set]
  rfl

theorem repMovsAfter_rsi (n len : Nat) (s : RamState) :
    rsi.read (repMovsAfter n len s) = rsi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repMovsAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repMovsAfter_rdi (n len : Nat) (s : RamState) :
    rdi.read (repMovsAfter n len s) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repMovsAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repMovsAfter_rcx (n len : Nat) (s : RamState) :
    rcx.read (repMovsAfter n len s) = rcx.read s - 1 := by
  simp [Operand.read, repMovsAfter_gpr, gprIndex]

theorem repMovsAfter_repeat (n len : Nat) (s : RamState) :
    (repMovsAfter n len s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  simp only [repMovsAfter, afterStep, finishStep, repCount, rcx_read_movsSpec]
  rfl

theorem repMovsAfter_rip (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repMovsAfter n len s).RIP =
      if rcx.read s - 1 = 0 then BitVec.add s.RIP (BitVec.ofNat 64 len) else s.RIP := by
  simp only [repMovsAfter, afterStep, finishStep, repCount, rcx_read_movsSpec]
  simp [movsSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem AgreesExcept.repMovs (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (n / 8), .rip] (clearRep s)
      (clearRep (repMovsAfter n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repMovsAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6, Ne.symm h7]
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
    rw [repMovsAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, clearRep, repMovsAfter, repCount, afterStep, finishStep, movsSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · simp only [clearRep_external] at hx ⊢
    rw [repMovsAfter_external]
    exact memStore_isSome _ _ _ x hx

theorem ReadyMidRep.repMovs [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat)
    (hdst : (rdi.read s).toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart (rdi.read s).toNat (n / 8)) :
    ReadyMidRep (repMovsAfter n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repMovsAfter n len s)).external := by
    rw [clearRep_external, repMovsAfter_external]
    exact IdentityPageTableMemory.memStore (ReadyToStep.memory (s := clearRep s) h).tables _ _
      hdst htables
  have : ReadyToStep (clearRep (repMovsAfter n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repMovs n len s) htab
  exact this

theorem repMovsAfter_copy (n len : Nat) (s : RamState) (hn : n ≤ 128) (i : Nat) (hi : i < n / 8)
    (hsrc : (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome) :
    (repMovsAfter n len s).external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[rsi.read s + BitVec.ofNat 64 i]? := by
  rw [repMovsAfter_external, memStore_getElem?_self _ _ _ hn i hi]
  simp only [Operand.read]
  rw [storedByte_memLoad _ _ i hi, memByte]
  simp only [PhysicalMemory.read]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsrc
  change some ((s.external[rsi.read s + BitVec.ofNat 64 i]?).getD 0) =
    s.external[rsi.read s + BitVec.ofNat 64 i]?
  rw [hb]
  rfl

def repMovsSegAfter (base : BitVec 64) (n len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repCount (movsSegSpec base n { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len) })

theorem repMovsSegAfter_external (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repMovsSegAfter base n len s).external =
      memStore s.external (rdi.read s) ((Operand.mem (base + rsi.read s) : Operand n).read s) := rfl

@[simp] theorem repMovsSegAfter_rflags (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repMovsSegAfter base n len s).RFLAGS = s.RFLAGS := rfl

theorem repMovsSegAfter_gpr (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repMovsSegAfter base n len s).GPR =
      Vector.set (Vector.set (Vector.set s.GPR 6 (s.GPR[6] + BitVec.ofNat _ (n / 8))) 7
        (s.GPR[7] + BitVec.ofNat _ (n / 8))) 1 (s.GPR[1] - 1) := by
  simp [repMovsSegAfter, repCount, afterStep, finishStep, movsSegSpec, Operand.write, Operand.read,
    dataAccess, afterFetches, beforeFetch, resetStepFields, gprIndex, mergeGPR_64, Vector.getElem_set]
  rfl

theorem repMovsSegAfter_rsi (base : BitVec 64) (n len : Nat) (s : RamState) :
    rsi.read (repMovsSegAfter base n len s) = rsi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repMovsSegAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repMovsSegAfter_rdi (base : BitVec 64) (n len : Nat) (s : RamState) :
    rdi.read (repMovsSegAfter base n len s) = rdi.read s + BitVec.ofNat 64 (n / 8) := by
  simp [Operand.read, repMovsSegAfter_gpr, gprIndex, Vector.getElem_set]
  rfl

theorem repMovsSegAfter_rcx (base : BitVec 64) (n len : Nat) (s : RamState) :
    rcx.read (repMovsSegAfter base n len s) = rcx.read s - 1 := by
  simp [Operand.read, repMovsSegAfter_gpr, gprIndex]

theorem rcx_read_movsSegSpec (base : BitVec 64) (n : Nat) (t : RamState) :
    rcx.read (movsSegSpec base n t) = rcx.read t := by
  simp only [movsSegSpec]
  rw [Operand.read_write_reg_of_ne _ (by decide), Operand.read_write_reg_of_ne _ (by decide),
    Operand.read_reg_write_mem, Operand.read_reg_dataAccess, Operand.read_reg_dataAccess]

theorem repMovsSegAfter_segReady (base : BitVec 64) (n len : Nat) (s : RamState) {r : SegReg} {b : BitVec 64}
    (h : r.Ready b s) : r.Ready b (repMovsSegAfter base n len s) := by
  have hfs : (repMovsSegAfter base n len s).FS = s.FS := by
    simp [repMovsSegAfter, repCount, afterStep, finishStep, movsSegSpec, Operand.write, dataAccess, afterFetches,
      beforeFetch, resetStepFields]
  have hgs : (repMovsSegAfter base n len s).GS = s.GS := by
    simp [repMovsSegAfter, repCount, afterStep, finishStep, movsSegSpec, Operand.write, dataAccess, afterFetches,
      beforeFetch, resetStepFields]
  obtain ⟨hs, hb⟩ := h
  cases r <;>
  · simp only [SegReg.read, SegReg.select, PrefixSegments.ofState] at hs hb
    exact ⟨by simpa [SegReg.read, SegReg.select, PrefixSegments.ofState, hfs, hgs] using hs,
      by simpa [SegReg.read, SegReg.select, PrefixSegments.ofState, hfs, hgs] using hb⟩

theorem repMovsSegAfter_repeat (base : BitVec 64) (n len : Nat) (s : RamState) :
    (repMovsSegAfter base n len s).Repeat_String_Operation = !(rcx.read s - 1 == 0#64) := by
  simp only [repMovsSegAfter, afterStep, finishStep, repCount, rcx_read_movsSegSpec]
  rfl

theorem repMovsSegAfter_rip (base : BitVec 64) (n len : Nat) (s : RamState) (hmsr : s.«MSRLIST::In_Process» = false) :
    (repMovsSegAfter base n len s).RIP =
      if rcx.read s - 1 = 0 then BitVec.add s.RIP (BitVec.ofNat 64 len) else s.RIP := by
  simp only [repMovsSegAfter, afterStep, finishStep, repCount, rcx_read_movsSegSpec]
  simp [movsSegSpec, Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields, hmsr]

theorem AgreesExcept.repMovsSeg (base : BitVec 64) (n len : Nat) (s : RamState) :
    AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (n / 8), .rip] (clearRep s)
      (clearRep (repMovsSegAfter base n len s)) := by
  refine ⟨fun c hc hm => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
  · cases c with
    | reg r =>
      have h1' : r ≠ 1 := fun h => hc (by simp [h])
      have h1 : r.toNat ≠ 1 := fun e => h1' (BitVec.eq_of_toNat_eq e)
      have h6' : r ≠ 6 := fun h => hc (by simp [h])
      have h6 : r.toNat ≠ 6 := fun e => h6' (BitVec.eq_of_toNat_eq e)
      have h7' : r ≠ 7 := fun h => hc (by simp [h])
      have h7 : r.toNat ≠ 7 := fun e => h7' (BitVec.eq_of_toNat_eq e)
      simp [Component.Agrees, clearRep, repMovsSegAfter_gpr, gprIndex, Ne.symm h1, Ne.symm h6, Ne.symm h7]
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
    rw [repMovsSegAfter_external]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hx (.mem (rdi.read s) (n / 8)) (by simp) ⟨i, hi, he.symm⟩
  · simp only [fixedPart, clearRep, repMovsSegAfter, repCount, afterStep, finishStep, movsSegSpec,
      Operand.write, dataAccess, afterFetches, beforeFetch, resetStepFields]
  · simp only [clearRep_external] at hx ⊢
    rw [repMovsSegAfter_external]
    exact memStore_isSome _ _ _ x hx

theorem ReadyMidRep.repMovsSeg [Bindings] {s : RamState} (h : ReadyMidRep s) (base : BitVec 64) (n len : Nat)
    (hdst : (rdi.read s).toNat + n / 8 ≤ 2^32)
    (htables : PageTableEntriesApart (rdi.read s).toNat (n / 8)) :
    ReadyMidRep (repMovsSegAfter base n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repMovsSegAfter base n len s)).external := by
    rw [clearRep_external, repMovsSegAfter_external]
    exact IdentityPageTableMemory.memStore (ReadyToStep.memory (s := clearRep s) h).tables _ _
      hdst htables
  have : ReadyToStep (clearRep (repMovsSegAfter base n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repMovsSeg base n len s) htab
  exact this

theorem repMovsSegAfter_copy (base : BitVec 64) (n len : Nat) (s : RamState) (hn : n ≤ 128) (i : Nat) (hi : i < n / 8)
    (hsrc : (s.external[base + rsi.read s + BitVec.ofNat 64 i]?).isSome) :
    (repMovsSegAfter base n len s).external[rdi.read s + BitVec.ofNat 64 i]? =
      s.external[base + rsi.read s + BitVec.ofNat 64 i]? := by
  rw [repMovsSegAfter_external, memStore_getElem?_self _ _ _ hn i hi]
  simp only [Operand.read]
  rw [storedByte_memLoad _ _ i hi, memByte]
  simp only [PhysicalMemory.read]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsrc
  change some ((s.external[base + rsi.read s + BitVec.ofNat 64 i]?).getD 0) =
    s.external[base + rsi.read s + BitVec.ofNat 64 i]?
  rw [hb]
  rfl

theorem rep_movsq_seg_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 8) (hwr : MemWritable s (rdi.read s) 8) :
    X86.Machine.step s = some (.next (repMovsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 64
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsq_seg_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hsr hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsq_scan_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsq_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsd_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 4) (hwr : MemWritable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repMovsAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsd_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsd_seg_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 4) (hwr : MemWritable s (rdi.read s) 4) :
    X86.Machine.step s = some (.next (repMovsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 32
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsd_seg_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw hseg hsr hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsd_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsd_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hosz hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsw_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 2) (hwr : MemWritable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repMovsAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsw_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsw_seg_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 2) (hwr : MemWritable s (rdi.read s) 2) :
    X86.Machine.step s = some (.next (repMovsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 16
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsw_seg_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hsr hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsw_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsw_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsb_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 1) (hwr : MemWritable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repMovsAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_rep_movsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsb_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA4 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA4 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsb_seg_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = true)
    (hsr : SegReady (scanContext s.DS (PrefixSegments.ofState s) pre).segment)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment + rsi.read s) 1) (hwr : MemWritable s (rdi.read s) 1) :
    X86.Machine.step s = some (.next (repMovsSegAfter (segBase (scanContext s.DS (PrefixSegments.ofState s) pre).segment) 8
      (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_rep_movsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsb_seg_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hseg hsr hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl)] at hdecode
  have hpreserve : scanPreservesRepeat (0xA4 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA4 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsb_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_rep_movsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsb_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA4 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA4 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsq_a32_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 8) (hwr : MemWritable s (rdi.read s) 8)
    (hsl : (rsi.read s).toNat + 8 < 2^32) (hdl : (rdi.read s).toNat + 8 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repMovsAfter 64 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsq_a32_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsq_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsq s h _ hrex2 hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsq_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsd_a32_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 4) (hwr : MemWritable s (rdi.read s) 4)
    (hsl : (rsi.read s).toNat + 4 < 2^32) (hdl : (rdi.read s).toNat + 4 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repMovsAfter 32 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsd_a32_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hosz hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsd_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsd s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsd_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hosz hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsw_a32_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 2) (hwr : MemWritable s (rdi.read s) 2)
    (hsl : (rsi.read s).toNat + 2 < 2^32) (hdl : (rdi.read s).toNat + 2 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repMovsAfter 16 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsw_a32_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hw hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsw_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA5]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA5]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA5]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A5_rep_movsw s h _ hrex2 hosz hw hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsw_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hw hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA5 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA5 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsb_a32_step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (s : RamState)
    (h : ReadyMidRep s) (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p)
    (hlen : pre.length ≤ 13)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hseg : (scanContext s.DS (PrefixSegments.ofState s) pre).seg_prefix_present = false)
    (hm64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hdf : DirectionFlagClear s.RFLAGS) (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s ≠ 0)
    (hrd : MemReadable s (rsi.read s) 1) (hwr : MemWritable s (rdi.read s) 1)
    (hsl : (rsi.read s).toNat + 1 < 2^32) (hdl : (rdi.read s).toNat + 1 < 2^32) (hcl : (rcx.read s).toNat < 2^32) :
    X86.Machine.step s = some (.next (repMovsAfter 8 (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_rep_movsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  have ht : DataReady (afterFetches (beforeFetch s) (pre.length + 2)) :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl hf.tables
  have hcpu := ReadyToStep.cpu (s := clearRep s) h
  rw [rep_movsb_a32_form hstride (afterFetches (beforeFetch s) (pre.length + 2)) _ _ ht (hmode _) haddr hrex2 hlock hseg hm64 hcpu.ds hcpu.es
    hdf hcount (hrd.of_external_eq rfl) (hwr.of_external_eq rfl) hsl hdl hcl] at hdecode
  have hpreserve : scanPreservesRepeat (0xA4 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA4 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

theorem rep_movsb_a32_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 13)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hrep : (scanContext s.DS (PrefixSegments.ofState s) pre).rep_prefix = 243)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hcode : BytesAt s s.RIP (pre ++ [0xA4]))
    (hlow : s.RIP.toNat + (pre.length + 1) ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (repZeroAfter (pre.length + 1) s)) := by
  have hlen' : (pre ++ [0xA4]).length = pre.length + 1 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0xA4]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hdecode := decodeLegacy0_run_of_A4_rep_movsb s h _ hrex2 hrep _
    pre.length (by omega) (by simp) hcode hlow'
  rw [rep_movsb_a32_form_zero (afterFetches (beforeFetch s) (pre.length + 2)) _ _ haddr hrex2 hlock hcount] at hdecode
  have hpreserve : scanPreservesRepeat (0xA4 : UInt8).toBitVec (scanContext s.DS (PrefixSegments.ofState s) pre) = true := by
    simp [scanPreservesRepeat, hrep]
  have hstep := step_scan_legacy0_midRep s _ h pre 0xA4 [] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2)).of_cs_lma_eq rfl rfl)
  rw [hpreserve] at hstep
  exact hstep

end X86Proofs
