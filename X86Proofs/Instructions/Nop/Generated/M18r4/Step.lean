import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Nop.Step
import X86Proofs.Instructions.NopMem.Step
import X86Proofs.Instructions.Nop.Generated.M18r4.Decode
import X86Proofs.Instructions.Nop.Generated.M18r4.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem nop_18r4_m_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, NopPrefix p) (hlen : pre.length ≤ 7) (am : AddrMode) (hv : am.Valid)
    (hb : am.rexB = 0) (hx : am.rexX = 0)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0x18 :: am.modrm 4 :: am.tail))
    (hlow : s.RIP.toNat + nopMemLen pre am ≤ 2^32) :
    X86.Machine.step s = some (.next (afterStep s (nopMemLen pre am) fun t =>
      withNextIP t (BitVec.add s.RIP (BitVec.ofNat 64 (nopMemLen pre am))))) := by
  have hlowN : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32 := hlow
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0x18 :: am.modrm 4 :: am.tail).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons]; omega
  have hdecode := decodeLegacy1_run_of_0F_18_r4_memory s h pre hpre (by omega)
    (am.modrm 4) (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    (by rw [AddrMode.modrmReg_modrm]) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0x0F :: 0x18 :: am.modrm 4 :: am.tail) := hcode
  have hctx := nopContext_scan s.DS (PrefixSegments.ofState s) pre hpre
  have hea := effectiveAddress_run (beforeFetch s) (pre.length + 4) h.fetchReady h.cpu.ds h.cpu.ss
    am hv (scanContext s.DS (PrefixSegments.ofState s) pre) (hctx.addrContext am hb hx) hc hlow' (pre.length + 3)
    (fun j _ => by
      rw [List.getElem?_append_right (by omega),
        show pre.length + 3 + j - pre.length = j + 1 + 1 + 1 by omega]
      rfl) (by simp; omega)
    (by have := am.tail_length_le; omega)
  rw [show pre.length + 4 + am.tail.length = nopMemLen pre am + 1 by simp only [nopMemLen]; omega]
    at hea
  replace hea : (Effective_Address 64 (scanContext s.DS (PrefixSegments.ofState s) pre) am.mod am.rm 1
      (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3)))).run
        (afterFetches (beforeFetch s) (pre.length + 4)) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (nopMemLen pre am)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (nopMemLen pre am + 1)) := hea
  rw [nop_18r4_m_form _ _ _ _ _ _ hctx.addr hctx.lock _ _ _ _ hea] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0x18 (am.modrm 4 :: am.tail)
    (nopPrefix_scanPrefix hpre) (by decide) (by omega) hcode hlow' hdecode
    (in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma)

end X86Proofs
