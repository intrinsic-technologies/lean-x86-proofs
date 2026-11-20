import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Mov.Generated.RImmC7.Decode
import X86Proofs.Instructions.Mov.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_r32_imm32_c7_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 32) (hcode : BytesAt s s.RIP (pre ++ 0xC7 :: modrm :: immBytes 32 imm))
    (hlow : s.RIP.toNat + (pre.length + 6) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 6) fun t =>
      writeResult t dst (movSpec (imm.signExtend 32))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6))))) := by
  intro ctx dst
  have hlen' : (pre ++ 0xC7 :: modrm :: immBytes 32 imm).length = pre.length + 6 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xC7 :: modrm :: immBytes 32 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C7_register s h _ pre.length modrm hmod hreg hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC7 :: modrm :: immBytes 32 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3) h.fetchReady hc
    hlow' 32 (by decide) imm (pre.length + 2)
    (fun j hj => by rw [getElem?_pre_tail]; exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  rw [mov_r_imm32_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) _ _
    32 (.inr rfl) hsize hlock imm himm (hmode _),
    add_ofNat_add, show pre.length + 2 + 4 = pre.length + 6 by omega,
    show pre.length + 3 + 32 / 8 = pre.length + 6 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre 0xC7 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 6 + 1)).of_cs_lma_eq rfl rfl)

theorem mov_r16_imm16_c7_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 16) (hcode : BytesAt s s.RIP (pre ++ 0xC7 :: modrm :: immBytes 16 imm))
    (hlow : s.RIP.toNat + (pre.length + 4) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4) fun t =>
      writeResult t dst (movSpec (imm.signExtend 16))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4))))) := by
  intro ctx dst
  have hlen' : (pre ++ 0xC7 :: modrm :: immBytes 16 imm).length = pre.length + 4 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xC7 :: modrm :: immBytes 16 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C7_register s h _ pre.length modrm hmod hreg hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC7 :: modrm :: immBytes 16 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3) h.fetchReady hc
    hlow' 16 (by decide) imm (pre.length + 2)
    (fun j hj => by rw [getElem?_pre_tail]; exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  rw [mov_r16_imm16_c7_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) _ _
    hsize hlock imm himm (hmode _),
    add_ofNat_add, show pre.length + 2 + 2 = pre.length + 4 by omega,
    show pre.length + 3 + 16 / 8 = pre.length + 4 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre 0xC7 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 4 + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
