import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Call.Step
import X86Proofs.Instructions.Pop.Generated.R.Decode
import X86Proofs.Instructions.Pop.Generated.R.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem pop_r64_8f_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = false)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hcode : BytesAt s s.RIP (pre ++ [0x8F, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 8) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      popState { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)) }
        (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm)))) := by
  intro ctx
  have hlen' : (pre ++ [0x8F, modrm]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x8F, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hdecode := decodeLegacy0_run_of_8F_pop_register s h _ pre.length modrm hmod hreg
    hcode hlow' (by simp) (by simp) (by omega) ctx hrex2
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 3)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 3)
  rw [pop_r_8f_form _ _ _ _ hmode64 hosz hlock hmode hd hss (hr.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x8F [modrm] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem pop_r16_8f_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 8)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (hmode64 : (scanContext s.DS (PrefixSegments.ofState s) pre).is_mode64 = true)
    (hosz : (scanContext s.DS (PrefixSegments.ofState s) pre).osz_prefix_present = true)
    (hw0 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 0)
    (modrm : UInt8) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hcode : BytesAt s s.RIP (pre ++ [0x8F, modrm]))
    (hlow : s.RIP.toNat + (pre.length + 2) ≤ 2^32)
    (hr : MemReadable s (stackPtr s) 2) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    X86.Machine.step s = some (.next (afterStep s (pre.length + 2) fun t =>
      popState16 { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2)) }
        (gprNumber ctx.rex_b4 ctx.rex_b3 (modrmRm modrm)))) := by
  intro ctx
  have hlen' : (pre ++ [0x8F, modrm]).length = pre.length + 2 := by simp
  have hlow' : s.RIP.toNat + (pre ++ [0x8F, modrm]).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hdecode := decodeLegacy0_run_of_8F_pop_register s h _ pre.length modrm hmod hreg
    hcode hlow' (by simp) (by simp) (by omega) ctx hrex2
  have hmode : In64BitMode (afterFetches (beforeFetch s) (pre.length + 3)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  obtain ⟨hd, hss⟩ := call_start h (pre.length + 3)
  rw [pop_r16_8f_form _ _ _ _ hmode64 hosz hw0 hlock hmode hd hss (hr.of_external_eq rfl)]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0x8F [modrm] hpre
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) (by omega) hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
