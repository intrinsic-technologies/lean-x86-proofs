import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Mov.Generated.R16Imm16.Decode
import X86Proofs.Instructions.Mov.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_r16_imm16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (op : UInt8) (hop : MovImmOpcode op)
    (imm : BitVec 16) (hcode : BytesAt s s.RIP (pre ++ op :: immBytes 16 imm))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (op.toBitVec.extractLsb' 0 3))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writeResult t dst (movSpec imm)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst
  have hlen' : (pre ++ op :: immBytes 16 imm).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ op :: immBytes 16 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hlegacy : LegacyOpcode op.toBitVec := by
    exact hop.legacyOpcode
  have hdecode := decodeLegacy0_run_of_movImm_at s h _ hrex2 op hop _ pre.length
    (by omega) (by simp) hcode hlow'
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ op :: immBytes 16 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 2) h.fetchReady hc
    hlow' 16 (by decide) imm (pre.length + 1)
    (fun j hj => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]
      exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  rw [mov_r16_imm16_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1))) _ _
    hsize hlock imm himm (hmode _),
    add_ofNat_add, show pre.length + 1 + 2 = pre.length + 3 by omega,
    show pre.length + 2 + 16 / 8 = pre.length + 3 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre op _ hpre
    hlegacy (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 3 + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
