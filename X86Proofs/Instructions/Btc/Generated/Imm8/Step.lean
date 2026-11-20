import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Btc.Generated.Imm8.Decode
import X86Proofs.Instructions.Btc.Generated.Imm8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem btc_r_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + (pre.length + 4) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4) fun t =>
      writeOutputs t dst
        (btcSpec (fun i => oracleBit (oracleSkip t.oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) (dst.read s) (imm.signExtend n)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4))))) := by
  intro ctx dst
  have hlen' : (pre ++ 0x0F :: 0xBA :: modrm :: immBytes 8 imm).length = pre.length + 4 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: 0xBA :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_BA_r7_register s h _ (pre.length + 1) modrm hmod hreg hcode
    hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2
  have hc2 : BytesAt s s.RIP ((pre ++ [0x0F]) ++ 0xBA :: modrm :: immBytes 8 imm) := by
    simpa using hcode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      ((pre ++ [0x0F]) ++ 0xBA :: modrm :: immBytes 8 imm) := hc2
  have hlen2 : ((pre ++ [0x0F]) ++ 0xBA :: modrm :: immBytes 8 imm).length =
      pre.length + 4 := by simp
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 1 + 3) h.fetchReady hc
    (by rw [hlen2]; exact hlow) 8 (by decide) imm ((pre ++ [0x0F]).length + 2)
    (fun j hj => by rw [getElem?_pre_tail]; exact immBytes_getElem? imm hj) (by simp)
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length + 2 = pre.length + 1 + 2 by simp] at himm
  rw [btc_r_imm8_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1 + 2))) _ _ imm
    (hmode _) n hn hsize hlock himm (hmode _), add_ofNat_add, show pre.length + 1 + 2 + 1 = pre.length + 4 by omega,
    show pre.length + 1 + 3 + 8 / 8 = pre.length + 4 + 1 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBA _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 4 + 1)).of_cs_lma_eq rfl rfl)

theorem btc_r16_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 7) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xBA :: modrm :: immBytes 8 imm))
    (hlow : s.RIP.toNat + (pre.length + 4) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4) fun t =>
      writeOutputs t dst
        (btcSpec (fun i => oracleBit (oracleSkip t.oracle i))
          (StatusFlags.ofRFLAGS t.RFLAGS) (dst.read s) (imm.signExtend 16)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4))))) := by
  intro ctx dst
  have hlen' : (pre ++ 0x0F :: 0xBA :: modrm :: immBytes 8 imm).length = pre.length + 4 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: 0xBA :: modrm :: immBytes 8 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy1_run_of_BA_r7_register s h _ (pre.length + 1) modrm hmod hreg hcode
    hlow' (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2
  have hc2 : BytesAt s s.RIP ((pre ++ [0x0F]) ++ 0xBA :: modrm :: immBytes 8 imm) := by
    simpa using hcode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      ((pre ++ [0x0F]) ++ 0xBA :: modrm :: immBytes 8 imm) := hc2
  have hlen2 : ((pre ++ [0x0F]) ++ 0xBA :: modrm :: immBytes 8 imm).length =
      pre.length + 4 := by simp
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 1 + 3) h.fetchReady hc
    (by rw [hlen2]; exact hlow) 8 (by decide) imm ((pre ++ [0x0F]).length + 2)
    (fun j hj => by rw [getElem?_pre_tail]; exact immBytes_getElem? imm hj) (by simp)
    (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length + 2 = pre.length + 1 + 2 by simp] at himm
  rw [btc_r16_imm8_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1 + 2))) _ _ imm
    (hmode _) hsize hlock himm (hmode _), add_ofNat_add, show pre.length + 1 + 2 + 1 = pre.length + 4 by omega,
    show pre.length + 1 + 3 + 8 / 8 = pre.length + 4 + 1 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xBA _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 4 + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
