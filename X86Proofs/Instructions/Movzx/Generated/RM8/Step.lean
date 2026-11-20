import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Instructions.Movzx.Generated.RM8.Decode
import X86Proofs.Instructions.Movzx.Generated.RM8.Form

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movzx_r_m8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length))) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 3 + am.tail.length))
    let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movzxSpec n ((Operand.mem addr : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy1_run_of_B6_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ (pre.length + 1) (by omega)
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xB6 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xB6 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0xB6 reg am hv [] _ hctx hcode2 hlow2 (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [movzx_r_m8_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) hread.low hread.mem]
    at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xB6 _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem movzx_r_m8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 3 + am.tail.length))) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movzxSpec n ((Operand.mem addr : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hdecode := decodeLegacy1_run_of_B6_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ (pre.length + 1) (by omega)
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xB6 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xB6 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0xB6 reg am hv [] _ hctx hcode2 hlow2 (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [movzx_r_m8_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) hread.low hread.mem]
    at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xB6 _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem movzx_r16_m8_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length))) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt s (pre.length + 3 + am.tail.length))
    let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movzxSpec 16 ((Operand.mem addr : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hdecode := decodeLegacy1_run_of_B6_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ (pre.length + 1) (by omega)
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xB6 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xB6 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea_seg s h (pre ++ [0x0F]) 0xB6 reg am hv [] _ hctx hcode2 hlow2 (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [movzx_r16_m8_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) hread.low hread.mem]
    at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xB6 _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem movzx_r16_m8_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 3 + am.tail.length))) 1) :
    let ctx := scanContext s.DS (PrefixSegments.ofState s) pre
    let addr := segAddr ctx (am.addrAt32 s (pre.length + 3 + am.tail.length))
    let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movzxSpec 16 ((Operand.mem addr : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro ctx addr dst
  have hlen' : (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0x0F :: 0xB6 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have h5 := am.tail_length_le
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hdecode := decodeLegacy1_run_of_B6_memory s h _ hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) _ (pre.length + 1) (by omega)
    (getElem?_pre_esc_op _ _ _ _) (getElem?_pre_esc_modrm _ _ _ _) hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hcode2 : BytesAt s s.RIP
      ((pre ++ [(0x0F : UInt8)]) ++ 0xB6 :: am.modrm reg :: (am.tail ++ [])) := by
    simpa using hcode
  have hlow2 : s.RIP.toNat +
      ((pre ++ [(0x0F : UInt8)]) ++ 0xB6 :: am.modrm reg :: (am.tail ++ [])).length ≤ 2^32 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hea := memAlu_ea32_seg s h (pre ++ [0x0F]) 0xB6 reg am hv [] _ hctx hcode2 hlow2 (by simp; omega)
  rw [show (pre ++ [(0x0F : UInt8)]).length = pre.length + 1 by simp,
    show pre.length + 1 + 2 + am.tail.length = pre.length + 3 + am.tail.length by omega,
    show pre.length + 1 + 3 + am.tail.length = pre.length + 3 + am.tail.length + 1 by omega] at hea
  rw [movzx_r16_m8_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ hea hrip _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hmode _) hread.low hread.mem]
    at hdecode
  simp only [Operand.read_afterFetches, Operand.read_beforeFetch] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy1 s _ h pre 0xB6 _ hpre ⟨by decide, by decide⟩ (by omega) hcode hlow'
    hdecode ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

theorem movzx_0FB6_memory_run [Bindings] (s : RamState) (h : ReadyToStep s)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false) (n : Nat)
    (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n) (haddr64 : ctx.address_size = 64)
    (hlock : ctx.lock_prefix_present = false) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hctx : AddrContext ctx am) (bytes : List UInt8) (k : Nat) (hk : k ≤ 2)
    (hb6 : bytes[k]? = some 0xB6) (hm : bytes[k + 1]? = some (am.modrm reg))
    (htail : ∀ j < am.tail.length, bytes[k + 2 + j]? = am.tail[j]?)
    (hlen : bytes.length = k + 2 + am.tail.length)
    (hcode : BytesAt s s.RIP bytes) (hlow : s.RIP.toNat + bytes.length ≤ 2^32)
    (hread : MemReadable s (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) 1) :
    let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 k)) ctx).run
        (afterFetches (beforeFetch s) (k + 1)) =
      some (.ok (), writeResult
        (dataAccess (afterFetches (beforeFetch s) (bytes.length + 1)) "load") dst
        (movzxSpec n ((Operand.mem (am.addr s (BitVec.add s.RIP
          (BitVec.ofNat 64 bytes.length))) : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))) := by
  intro dst
  have hdecode := decodeLegacy1_run_of_B6_memory s h ctx hrex2 (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) bytes k (by omega) hb6 hm hcode hlow
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP bytes := hcode
  have hea := effectiveAddress_run (beforeFetch s) (k + 3) h.fetchReady h.cpu.ds h.cpu.ss am hv
    ctx hctx hc hlow (k + 2) htail (by omega) (by have := am.tail_length_le; omega)
  rw [show k + 3 + am.tail.length = bytes.length + 1 by omega,
    show k + 2 + am.tail.length = bytes.length by omega] at hea
  let t := afterFetches (beforeFetch s) (bytes.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t :=
    h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length)) =
      am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length)) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 bytes.length))
  rw [haddr] at hrip
  replace hea : (Effective_Address 64 ctx am.mod am.rm 1
      (BitVec.add s.RIP (BitVec.ofNat 64 (k + 2)))).run (afterFetches (beforeFetch s) (k + 3)) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 bytes.length), am.isRip, am.baseUsesRsp), t) := hea
  rw [movzx_r_m8_form _ t _ _ _ _ _ n hn hsize haddr64 hlock _ _ _ _ _ hea hrip _
    (SegAccess.flat _ _) ht hmode hread.low hread.mem] at hdecode
  exact hdecode

theorem movzx_r32_m8_step [Bindings] (s : RamState) (h : ReadyToStep s) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0)
    (hcode : BytesAt s s.RIP (0x0F :: 0xB6 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))
      1) :
    let dst : Operand 32 := .reg (gprNumber 0 0 reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movzxSpec 32 ((Operand.mem (am.addr s (BitVec.add s.RIP
          (BitVec.ofNat 64 (3 + am.tail.length)))) : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro dst
  have hlen : (0x0F :: 0xB6 :: am.modrm reg :: am.tail : List UInt8).length = 3 + am.tail.length :=
    by simp only [List.length_cons]; omega
  have hlow' : s.RIP.toNat + (0x0F :: 0xB6 :: am.modrm reg :: am.tail : List UInt8).length ≤ 2^32 :=
    by rw [hlen]; exact hlow
  have hctx : AddrContext (legacyContext s.DS) am := ⟨rfl, rfl, rfl, rfl, hb.symm, hx.symm⟩
  have hdecode := movzx_0FB6_memory_run s h (legacyContext s.DS) rfl 32 (.inr rfl) rfl rfl rfl
    reg am hv hctx _ 1 (by decide) rfl rfl
    (fun j _ => by rw [show 1 + 2 + j = j + 1 + 1 + 1 by omega]; rfl)
    (by simp only [List.length_cons]; omega)
    hcode hlow' (by rw [hlen]; exact hread)
  rw [hlen] at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (3 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0xB6 _ ⟨by decide, by decide⟩ hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem movzx_r_m8_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (rexContext s.DS rex.toBitVec).operand_size = n) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x0F :: 0xB6 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addr s (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))
      1) :
    let dst : Operand n := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (4 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movzxSpec n ((Operand.mem (am.addr s (BitVec.add s.RIP
          (BitVec.ofNat 64 (4 + am.tail.length)))) : Operand 8).read s))
        (BitVec.add s.RIP (BitVec.ofNat 64 (4 + am.tail.length))))) := by
  intro dst
  have hlen : (rex :: 0x0F :: 0xB6 :: am.modrm reg :: am.tail : List UInt8).length =
      4 + am.tail.length := by simp only [List.length_cons]; omega
  have hlow' : s.RIP.toNat + (rex :: 0x0F :: 0xB6 :: am.modrm reg :: am.tail : List UInt8).length
      ≤ 2^32 := by rw [hlen]; exact hlow
  have hdecode := movzx_0FB6_memory_run s h (rexContext s.DS rex.toBitVec) rfl n hn hsize rfl rfl
    reg am hv (AddrContext.rex _ _ am hx hb) _ 2 (by decide) rfl rfl
    (fun j _ => by rw [show 2 + 2 + j = j + 1 + 1 + 1 + 1 by omega]; rfl)
    (by simp only [List.length_cons]; omega)
    hcode hlow' (by rw [hlen]; exact hread)
  rw [hlen] at hdecode
  have hmode : In64BitMode (afterFetches (beforeFetch s) (4 + am.tail.length + 1)) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0xB6 _ hrex ⟨by decide, by decide⟩ hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
