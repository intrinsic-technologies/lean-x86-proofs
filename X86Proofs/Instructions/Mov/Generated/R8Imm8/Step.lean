import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Decode
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_r8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (op : UInt8) (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7])
    (hrm : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3
        (op.toBitVec.extractLsb' 0 3)).toNat < 4)
    (imm : BitVec 8) (hcode : BytesAt s s.RIP (pre ++ op :: immBytes 8 imm))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (op.toBitVec.extractLsb' 0 3))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      writeResult t dst (movSpec imm)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))))) := by
  intro ctx dst
  have hlen' : (pre ++ op :: immBytes 8 imm).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ op :: immBytes 8 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hlegacy : LegacyOpcode op.toBitVec := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact legacyOpcode_of_check _ ⟨by decide, by decide⟩
  have hdecode := decodeLegacy0_run_of_movImm8_at s h _ hrex2 op hop _ pre.length
    (by omega) (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ op :: immBytes 8 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 8 (by decide) imm (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  rw [mov_r8_imm8_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ _
    hrm hlock imm himm (hmode _),
    add_ofNat_add, show pre.length + 1 + 1 = pre.length + 2 by omega,
    show pre.length + 2 + 8 / 8 = pre.length + 2 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre op _ hpre
    hlegacy (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + 1)).of_cs_lma_eq rfl rfl)

theorem mov_r8_imm8_gpr8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (op : UInt8) (hop : op ∈ [0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7])
    (imm : BitVec 8) (hcode : BytesAt s s.RIP (pre ++ op :: immBytes 8 imm))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 :=
      .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 (op.toBitVec.extractLsb' 0 3)) (byteRex ctx)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      writeResult t dst (movSpec imm)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))))) := by
  intro ctx dst
  have hlen' : (pre ++ op :: immBytes 8 imm).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ op :: immBytes 8 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hlegacy : LegacyOpcode op.toBitVec := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact legacyOpcode_of_check _ ⟨by decide, by decide⟩
  have hdecode := decodeLegacy0_run_of_movImm8_at s h _ hrex2 op hop _ pre.length
    (by omega) (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ op :: immBytes 8 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 8 (by decide) imm (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  rw [mov_r8_imm8_gpr8_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ _
    hlock imm himm (hmode _),
    add_ofNat_add, show pre.length + 1 + 1 = pre.length + 2 by omega,
    show pre.length + 2 + 8 / 8 = pre.length + 2 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre op _ hpre
    hlegacy (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 2 + 1)).writeResult _ _ _)

end X86Proofs
