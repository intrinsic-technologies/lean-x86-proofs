import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Mov.Generated.R8Imm8C6.Decode
import X86Proofs.Instructions.Mov.Generated.R8Imm8C6.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem mov_r8_imm8_c6_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hrm : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_prefix_present = true ∨
      (gprNumber (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b4 (scanContext s.DS (PrefixSegments.ofState s) pre).rex_b3
        (modrmRm modrm)).toNat < 4)
    (imm : BitVec 8) (hcode : BytesAt s s.RIP (pre ++ 0xC6 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writeResult t dst (movSpec imm)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst
  have hlen' : (pre ++ 0xC6 :: modrm :: immBytes 8 imm).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xC6 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C6_register s h _ pre.length modrm hmod hreg hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC6 :: modrm :: immBytes 8 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3) h.fetchReady hc
    hlow' 8 (by decide) imm (pre.length + 2)
    (fun j hj => by rw [getElem?_pre_tail]; exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  rw [mov_r8_imm8_c6_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) _ _
    hrm hlock imm himm (hmode _),
    add_ofNat_add, show pre.length + 2 + 1 = pre.length + 3 by omega,
    show pre.length + 3 + 8 / 8 = pre.length + 3 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre 0xC6 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 3 + 1)).of_cs_lma_eq rfl rfl)

theorem mov_r8_imm8_c6_gpr8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 8) (hcode : BytesAt s s.RIP (pre ++ 0xC6 :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + (pre.length + 3) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 8 :=
      .gpr8 (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm)) (byteRex ctx)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3) fun t =>
      writeResult t dst (movSpec imm)
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3))))) := by
  intro ctx dst
  have hlen' : (pre ++ 0xC6 :: modrm :: immBytes 8 imm).length = pre.length + 3 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0xC6 :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C6_register s h _ pre.length modrm hmod hreg hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC6 :: modrm :: immBytes 8 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3) h.fetchReady hc
    hlow' 8 (by decide) imm (pre.length + 2)
    (fun j hj => by rw [getElem?_pre_tail]; exact immBytes_getElem? imm hj)
    (by rw [hlen']; omega) (by omega)
  rw [mov_r8_imm8_c6_gpr8_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) _ _
    hlock imm himm (hmode _),
    add_ofNat_add, show pre.length + 2 + 1 = pre.length + 3 by omega,
    show pre.length + 3 + 8 / 8 = pre.length + 3 + 1 by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · first | exact h.ready.repeatClear | (simp only [writeResult, Operand.write_repeat]; exact h.ready.repeatClear)
  exact step_scan_legacy0 s _ h pre 0xC6 _ hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 3 + 1)).writeResult _ _ _)

end X86Proofs
