import X86Proofs.Step.AfterStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Imul.Generated.RRImm32.Decode
import X86Proofs.Instructions.Imul.Generated.RRImm32.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem imul_r_r_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (pre ++ 0x69 :: modrm :: immBytes 32 imm))
    (hlow : s.RIP.toNat + (pre.length + 6) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
    let src : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 6) fun t =>
      writeOutputs t dst
        (imulSpec (fun i => oracleBit (oracleSkip t.oracle i)) (src.read s) (imm.signExtend n)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6))))) := by
  intro ctx dst src
  have hlen' : (pre ++ 0x69 :: modrm :: immBytes 32 imm).length = pre.length + 6 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0x69 :: modrm :: immBytes 32 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_69_register s h _ pre.length modrm hmod hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x69 :: modrm :: immBytes 32 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3) h.fetchReady hc hlow'
    32 (by decide) imm (pre.length + 2)
    (fun j hj => by rw [getElem?_pre_tail]; exact immBytes_getElem? imm hj) (by rw [hlen']; omega)
    (by omega)
  rw [imul_r_r_imm32_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) _ _ _ imm (hmode _) n hn hsize
    hlock himm (hmode _), add_ofNat_add, show pre.length + 2 + 4 = pre.length + 6 by omega,
    show pre.length + 3 + 32 / 8 = pre.length + 6 + 1 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x69 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 6 + 1)).of_cs_lma_eq rfl rfl)

theorem imul_r16_r16_imm16_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (imm : BitVec 16)
    (hcode : BytesAt s s.RIP (pre ++ 0x69 :: modrm :: immBytes 16 imm))
    (hlow : s.RIP.toNat + (pre.length + 4) ≤ 2^32) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 (modrmReg modrm))
    let src : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4) fun t =>
      writeOutputs t dst
        (imulSpec (fun i => oracleBit (oracleSkip t.oracle i)) (src.read s) (imm.signExtend 16)) 4
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4))))) := by
  intro ctx dst src
  have hlen' : (pre ++ 0x69 :: modrm :: immBytes 16 imm).length = pre.length + 4 := by simp
  have hlow' : s.RIP.toNat + (pre ++ 0x69 :: modrm :: immBytes 16 imm).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_69_register s h _ pre.length modrm hmod hcode hlow'
    (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x69 :: modrm :: immBytes 16 imm) := hcode
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3) h.fetchReady hc hlow'
    16 (by decide) imm (pre.length + 2)
    (fun j hj => by rw [getElem?_pre_tail]; exact immBytes_getElem? imm hj) (by rw [hlen']; omega)
    (by omega)
  rw [imul_r16_r16_imm16_form _ _ (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2))) _ _ _ imm (hmode _) hsize
    hlock himm (hmode _), add_ofNat_add, show pre.length + 2 + 2 = pre.length + 4 by omega,
    show pre.length + 3 + 16 / 8 = pre.length + 4 + 1 by omega] at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x69 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode ((hmode (pre.length + 4 + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
