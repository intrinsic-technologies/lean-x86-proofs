import X86Proofs.Step.AfterStep
import X86Proofs.Instructions.Cmpxchg16b.Generated.M128Lock.Decode
import X86Proofs.Instructions.Cmpxchg16b.Generated.M128Lock.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmpxchg16b_lock_m128_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (hcx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length))) 16)
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length))) 16) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length))
    let x := (Operand.mem addr : Operand 128).read s
    let acc := (Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s
    let rep := (Operand.reg 1 : Operand 64).read s ++ (Operand.reg 3 : Operand 64).read s
    let out := cmpxchg16bSpec (StatusFlags.ofRFLAGS s.RFLAGS) acc rep x
    let next := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      if acc = x then writeRmwOutputs t addr out 0 next
      else
        writeRmwRegPairOutputs t addr out 0 next 2 (x.extractLsb' 64 64) 0 (x.setWidth 64))) := by
  intro addr x acc rep out next
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hdecode := decodeLegacy1_run_of_C7_r1_memory_w_lock s h hcx _ (pre.length + 1)
    (am.modrm 1) (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    (AddrMode.modrmReg_modrm _ _) hcode hlow' (getElem?_pre_esc_op _ _ _ _)
    (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hw hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xC7 :: am.modrm 1 :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xC7 :: am.modrm 1 :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0xC7 1 am hv [] _ hctx hcode2 hlow2 (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s) next
  rw [AddrMode.addr_of_gpr rfl] at hrip
  rw [cmpxchg16b_lock_m128_form _ t _ _ _ _ haddr hw _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem
    (memAlu_lockReady hlk _)]
    at hdecode
  simp only [t, Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
    beforeFetch_RFLAGS] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · split <;> exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xC7 _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode (hmode.of_cs_lma_eq (by dsimp only; split <;> rfl) (by dsimp only; split <;> rfl))

theorem cmpxchg16b_lock_m128_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hw : (scanContext s.DS (PrefixSegments.ofState s) pre).rex_w = 1)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = true)
    (hcx : Prelude.ReportsCPUFeature Bindings.processor s CPUID_CMPXCHG16B_Encoding true)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xC7 :: am.modrm 1 :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 3 + am.tail.length))) 16)
    (hlk : LockReady s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 3 + am.tail.length))) 16) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let x := (Operand.mem addr : Operand 128).read s
    let acc := (Operand.reg 2 : Operand 64).read s ++ (Operand.reg 0 : Operand 64).read s
    let rep := (Operand.reg 1 : Operand 64).read s ++ (Operand.reg 3 : Operand 64).read s
    let out := cmpxchg16bSpec (StatusFlags.ofRFLAGS s.RFLAGS) acc rep x
    let next := BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      if acc = x then writeRmwOutputs t addr out 0 next
      else
        writeRmwRegPairOutputs t addr out 0 next 2 (x.extractLsb' 64 64) 0 (x.setWidth 64))) := by
  intro addr x acc rep out next
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat + (pre ++ 0x0F :: 0xC7 :: am.modrm 1 :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hdecode := decodeLegacy1_run_of_C7_r1_memory_w_lock s h hcx _ (pre.length + 1)
    (am.modrm 1) (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three)
    (AddrMode.modrmReg_modrm _ _) hcode hlow' (getElem?_pre_esc_op _ _ _ _)
    (getElem?_pre_esc_modrm _ _ _ _) (by omega) _ hrex2 hw hlock
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xC7 :: am.modrm 1 :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xC7 :: am.modrm 1 :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0xC7 1 am hv [] _ hctx hcode2 hlow2 (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  let t := afterFetches (beforeFetch s) (pre.length + 3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s) next
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  rw [cmpxchg16b_lock_m128_form _ t _ _ _ _ haddr hw _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) hread.low hread.mem
    (memAlu_lockReady hlk _)]
    at hdecode
  simp only [t, Operand.read_afterFetches, Operand.read_beforeFetch, afterFetches_RFLAGS,
    beforeFetch_RFLAGS] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · split <;> exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xC7 _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode (hmode.of_cs_lma_eq (by dsimp only; split <;> rfl) (by dsimp only; split <;> rfl))

end X86Proofs
