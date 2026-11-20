import X86Proofs.Step.AfterStep
import X86Proofs.Step.PrefixScan
import X86Proofs.Instructions.MovLoad.Step
import X86Proofs.Instructions.MovStore.Decode
import X86Proofs.Instructions.MovStore.Form
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Decode

/-!
# Layer 3: store step theorems

A memory operand given by an `AddrMode` `am`; `len` is the instruction length and the operand's
address is `am.addrAt s len = am.addr s (RIP + len)` (relative to the instruction's end for a
RIP-relative operand):

- `mov_m64_r64_step` / `mov_m32_r32_step`: `rex 89 /r` (REX.W / W = 0), `len = 3 + am.tail.length`.
- `mov_m64_imm32_step`: `REX.W C7 /0 id`, the immediate sign-extended to 64 bits,
  `len = 7 + am.tail.length`.
- `mov_m16_imm16_step`: `66 C7 /0 iw` (operand size 16, no REX: `am` must not need REX.X/REX.B),
  `len = 5 + am.tail.length`.
- `mov_m8_imm8_step`: `C6 /0 ib` (no prefix, no REX), `len = 3 + am.tail.length`.
- `mov_m_imm32_prefix_step` (operand size 64 or 32), `mov_m16_imm16_prefix_step`,
  `mov_m8_imm8_prefix_step`: `C7 /0` / `C6 /0` after any prefix list the scan covers, including an
  FS/GS segment override (`SegAddrContext`; the store is at `segAddr ctx (am.addrAt s len)`);
  `mov_m_imm32_prefix_a32_step`, `mov_m16_imm16_prefix_a32_step`, `mov_m8_imm8_prefix_a32_step`:
  the same at address size 32 (a `67` prefix; the store at `segAddr ctx (am.addrAt32 s len)`).

Each result is `afterStep s len fun t => writeResult (dataAccess t "store") (.mem addr) v
(RIP + len)` with `v` computed from `s`. Preservation and frame: `Program/ReadWrite/Store.lean`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem getElem?_cons3_append (a b c : UInt8) (l m : List UInt8) (j : Nat) (hj : j < l.length) :
    (a :: b :: c :: (l ++ m))[3 + j]? = l[j]? := by
  rw [getElem?_cons3, List.getElem?_append_left hj]

theorem getElem?_cons2_append (a b : UInt8) (l m : List UInt8) (j : Nat) (hj : j < l.length) :
    (a :: b :: (l ++ m))[2 + j]? = l[j]? := by
  rw [show 2 + j = j + 1 + 1 by omega, List.getElem?_cons_succ, List.getElem?_cons_succ,
    List.getElem?_append_left hj]

/-! ### `89 /r` -/

/-- The common part of the 64- and 32-bit `rex 89` step theorems. -/
theorem mov_rex_89_memory_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (rexContext s.DS rex.toBitVec).operand_size = n) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (3 + am.tail.length)) (n / 8)) :
    let src : Operand n := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand n)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro src
  have hlow' : s.RIP.toNat + (rex :: 0x89 :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_pfx_89_memory s h rex (am.modrm reg) (rexContext s.DS rex.toBitVec) rfl
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x89 :: am.modrm reg :: am.tail) :=
    hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 3
    (fun j _ => getElem?_cons3 _ _ _ _ j) (by simp; omega) (by have := am.tail_length_le; omega)
  rw [show 4 + am.tail.length = 3 + am.tail.length + 1 by omega] at hea
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + am.tail.length + 1)) := hea
  let t := afterFetches (beforeFetch s) (3 + am.tail.length + 1)
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have ht : DataReady t := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have haddr : am.addr (beforeFetch s) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) =
      am.addrAt s (3 + am.tail.length) := AddrMode.addr_of_gpr rfl _
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)))
  rw [haddr] at hrip
  rw [mov_m_r_form _ t _ _ _ _ _ n hn hsize rfl rfl _ _ _ _ _ hea hrip _ (SegAccess.flat _ _) ht
    hmode (hw.of_external_eq rfl)] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x89 _ hrex (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 3 for `mov [mem], r64` (`REX.W 89 /r`, `mod ≠ 3`), for any source of the 16 registers and
any addressing shape `am` (REX.X and REX.B as `am` needs). If the machine is ready to step, the
instruction is at RIP below 4 GiB, and the 8 bytes at `am.addrAt s len` can be written in place
(`MemWritable`), one `step` stores the `reg` register (extended by REX.R) there, with
`Next_IP` = RIP + `len`.
-/
theorem mov_m64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (3 + am.tail.length)) 8) :
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 64)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  mov_rex_89_memory_step s h rex hrex.rexPrefix 64 (.inl rfl) (hrex.operand_size s.DS) reg am hv
    hx hb hcode hlow hw

/-- Layer 3 for `mov [mem], r32` (`REX 89 /r` with W = 0, `mod ≠ 3`): as `mov_m64_r64_step`,
storing the low 4 bytes of the register. -/
theorem mov_m32_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x89 :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (3 + am.tail.length)) 4) :
    let src : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 32)
        (movSpec (src.read s)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  mov_rex_89_memory_step s h rex hrex.rexPrefix 32 (.inr rfl) (hrex.operand_size s.DS) reg am hv
    hx hb hcode hlow hw

/-! ### `C7 /0` -/

/--
Layer 3 for `mov qword [mem], imm32` (`REX.W C7 /0 id`, `mod ≠ 3`), for any addressing shape
`am` (REX.X and REX.B as `am` needs): the instruction `rex, C7, am.modrm 0, am.tail, imm`,
`len = 7 + am.tail.length` bytes. If the 8 bytes at `am.addrAt s len` can be written in place,
one `step` stores the immediate sign-extended to 64 bits there, with `Next_IP` = RIP + `len`.
-/
theorem mov_m64_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (7 + am.tail.length)) 8) :
    X86.Machine.step s = some (.next (afterStep s (7 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (7 + am.tail.length)) : Operand 64)
        (movSpec (imm.signExtend 64)) (BitVec.add s.RIP (BitVec.ofNat 64 (7 + am.tail.length))))) := by
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length ≤
      2^32 := by
    simp only [List.length_cons, List.length_append, immBytes_length]; omega
  have hdecode := decodeLegacy0_run_of_pfx_C7_memory s h rex (am.modrm 0) (rexContext s.DS rex.toBitVec) rfl
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) _ hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (rex :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (rexContext s.DS rex.toBitVec) (AddrContext.rex _ _ am hx hb) hc hlow' 3
    (fun j hj => getElem?_cons3_append _ _ _ _ _ j hj) (by simp; omega) (by omega)
  replace hea : (Effective_Address 64 (rexContext s.DS rex.toBitVec) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (4 + am.tail.length)) := hea
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (4 + am.tail.length) h.fetchReady hc hlow' 32
    (by decide) imm (3 + am.tail.length)
    (fun j hj => by
      have := immBytes_getElem?_append (rex :: 0xC7 :: am.modrm 0 :: am.tail) imm j hj
      simp only [List.length_cons, List.cons_append] at this
      rwa [show am.tail.length + 1 + 1 + 1 + j = 3 + am.tail.length + j by omega] at this)
    (by simp; omega) (by omega)
  rw [show 4 + am.tail.length + 32 / 8 = 7 + am.tail.length + 1 by omega] at himm
  let u := afterFetches (beforeFetch s) (7 + am.tail.length + 1)
  have hu : DataReady u := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hend : BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) 4#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (7 + am.tail.length)) := by
    have := add_ofNat_add s.RIP (3 + am.tail.length) 4
    rw [show 3 + am.tail.length + 4 = 7 + am.tail.length by omega] at this
    exact this
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) 4#64)
  rw [show am.addr (beforeFetch s) _ = am.addrAt s (7 + am.tail.length) by
    rw [hend]; exact AddrMode.addr_of_gpr rfl _] at hrip
  rw [mov_m_imm32_form _ _ u _ _ _ _ 64 (.inl rfl) (hrex.operand_size s.DS) rfl rfl _ _ _ _ _ imm
    hea himm hrip _ (SegAccess.flat _ _) hu (hw.of_external_eq rfl), hend] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC7 _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 3 for `mov word [mem], imm16` (`66 C7 /0 iw`, `mod ≠ 3`), for an addressing shape `am`
that needs neither REX.X nor REX.B: the instruction `66, C7, am.modrm 0, am.tail, imm`,
`len = 5 + am.tail.length` bytes. If the 2 bytes at `am.addrAt s len` can be written in place,
one `step` stores the immediate there, with `Next_IP` = RIP + `len`.
-/
theorem mov_m16_imm16_step [Bindings] (s : RamState) (h : ReadyToStep s) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 16)
    (hcode : BytesAt s s.RIP (0x66 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)))
    (hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (5 + am.tail.length)) 2) :
    X86.Machine.step s = some (.next (afterStep s (5 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (5 + am.tail.length)) : Operand 16)
        (movSpec (imm.signExtend 16)) (BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length))))) := by
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (0x66 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)).length ≤
      2^32 := by
    simp only [List.length_cons, List.length_append, immBytes_length]; omega
  have hdecode := decodeLegacy0_run_of_pfx_C7_memory s h 0x66 (am.modrm 0) (oszContext s.DS) rfl
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) _ hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0x66 :: 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 4 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (oszContext s.DS) (AddrContext.osz _ am hx hb) hc hlow' 3
    (fun j hj => getElem?_cons3_append _ _ _ _ _ j hj) (by simp; omega) (by omega)
  replace hea : (Effective_Address 64 (oszContext s.DS) am.mod am.rm 1
      (BitVec.add s.RIP 3#64)).run (afterFetches (beforeFetch s) 4) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (4 + am.tail.length)) := hea
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (4 + am.tail.length) h.fetchReady hc hlow' 16
    (by decide) imm (3 + am.tail.length)
    (fun j hj => by
      have := immBytes_getElem?_append (0x66 :: 0xC7 :: am.modrm 0 :: am.tail) imm j hj
      simp only [List.length_cons, List.cons_append] at this
      rwa [show am.tail.length + 1 + 1 + 1 + j = 3 + am.tail.length + j by omega] at this)
    (by simp; omega) (by omega)
  rw [show 4 + am.tail.length + 16 / 8 = 5 + am.tail.length + 1 by omega] at himm
  let u := afterFetches (beforeFetch s) (5 + am.tail.length + 1)
  have hu : DataReady u := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hend : BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) 2#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (5 + am.tail.length)) := by
    have := add_ofNat_add s.RIP (3 + am.tail.length) 2
    rw [show 3 + am.tail.length + 2 = 5 + am.tail.length by omega] at this
    exact this
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))) 2#64)
  rw [show am.addr (beforeFetch s) _ = am.addrAt s (5 + am.tail.length) by
    rw [hend]; exact AddrMode.addr_of_gpr rfl _] at hrip
  rw [mov_m_imm16_form (asz := 64) _ _ u _ _ _ _ rfl rfl rfl _ _ _ _ _ imm hea himm hrip _
    (SegAccess.flat _ _) hu (hw.of_external_eq rfl), hend] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_66_legacy0 s _ h 0xC7 _ (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow'
    hdecode (hmode.of_cs_lma_eq rfl rfl)

/-! ### `C6 /0` -/

/--
Layer 3 for `mov byte [mem], imm8` (`C6 /0 ib`, `mod ≠ 3`, no prefix), for an addressing shape
`am` that needs neither REX.X nor REX.B: the instruction `C6, am.modrm 0, am.tail, imm`,
`len = 3 + am.tail.length` bytes. If the byte at `am.addrAt s len` can be written in place,
one `step` stores the immediate there, with `Next_IP` = RIP + `len`.
-/
theorem mov_m8_imm8_step [Bindings] (s : RamState) (h : ReadyToStep s) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (am.addrAt s (3 + am.tail.length)) 1) :
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem (am.addrAt s (3 + am.tail.length)) : Operand 8)
        (movSpec (imm.signExtend 8)) (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  have htl := am.tail_length_le
  have hlow' : s.RIP.toNat + (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length ≤
      2^32 := by
    simp only [List.length_cons, List.length_append, immBytes_length]; omega
  have hdecode := decodeLegacy0_run_of_C6_memory s h (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (by rw [AddrMode.modrmReg_modrm]) _ hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hea := effectiveAddress_run (beforeFetch s) 3 h.fetchReady h.cpu.ds h.cpu.ss am hv
    (legacyContext s.DS) (AddrContext.legacy _ am hx hb) hc hlow' 2
    (fun j hj => getElem?_cons2_append _ _ _ _ j hj) (by simp; omega) (by omega)
  have himm := memFetch_run_of_bytesAt_imm (beforeFetch s) (3 + am.tail.length) h.fetchReady hc hlow' 8
    (by decide) imm (2 + am.tail.length)
    (fun j hj => by
      have := immBytes_getElem?_append (0xC6 :: am.modrm 0 :: am.tail) imm j hj
      simp only [List.length_cons, List.cons_append] at this
      rwa [show am.tail.length + 1 + 1 + j = 2 + am.tail.length + j by omega] at this)
    (by simp; omega) (by omega)
  rw [show 3 + am.tail.length + 8 / 8 = 3 + am.tail.length + 1 by omega] at himm
  let u := afterFetches (beforeFetch s) (3 + am.tail.length + 1)
  have hu : DataReady u := h.dataReady.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl rfl rfl rfl rfl h.memory.tables
  have hmode : In64BitMode u := in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hend : BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) 1#64 =
      BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length)) := by
    have := add_ofNat_add s.RIP (2 + am.tail.length) 1
    rw [show 2 + am.tail.length + 1 = 3 + am.tail.length by omega] at this
    exact this
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length))) 1#64)
  rw [show am.addr (beforeFetch s) _ = am.addrAt s (3 + am.tail.length) by
    rw [hend]; exact AddrMode.addr_of_gpr rfl _] at hrip
  have hea' : (Effective_Address 64 (legacyContext s.DS) am.mod am.rm 1
      (BitVec.add s.RIP 2#64)).run (afterFetches (beforeFetch s) 3) =
      (.ok (am.offset (beforeFetch s), flatData am.isStack,
        BitVec.add s.RIP (BitVec.ofNat 64 (2 + am.tail.length)), am.isRip, am.baseUsesRsp),
        afterFetches (beforeFetch s) (3 + am.tail.length)) := hea
  rw [mov_m8_imm8_form (asz := 64) _ _ u _ _ _ _ rfl rfl _ _ _ _ _ imm hea' himm hrip _
    (SegAccess.flat _ _) hu (hw.of_external_eq rfl), hend] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0xC6 _ (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode
    hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

/-! ### Any prefix list (segment overrides) -/

/--
Layer 3 for `mov [mem], imm32` (`C7 /0 id`, `mod ≠ 3`) after any prefix list `pre` the prefix
scan covers that selects operand size `n` (64 or 32), including an FS/GS segment override
(`SegAddrContext`): the instruction `pre ++ C7, am.modrm 0, am.tail, imm`, `len = pre.length + 6 +
am.tail.length` bytes. If the `n / 8` bytes at the operand's linear address (`segAddr`: the
offset `am.addrAt s len`, plus the segment's base after an FS/GS prefix) can be written in place,
one `step` stores the immediate sign-extended to `n` bits there.
-/
theorem mov_m_imm32_prefix_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 4) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (pre.length + 6 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 6 + am.tail.length))) (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 6 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 6 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand n) (movSpec (imm.signExtend n))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length =
      pre.length + 6 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C7_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xC7 0 am hv (immBytes 32 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 32 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC7 (am.modrm 0) am.tail imm) (by rw [hlen']; omega)
    (by omega)
  rw [show pre.length + 3 + am.tail.length + 32 / 8 = pre.length + 6 + am.tail.length + 1 by
    omega] at hfetch
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 4#64) =
        .ok (am.addrAt s (pre.length + 6 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by omega]
    exact hrip
  rw [mov_m_imm32_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ imm hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hw.of_external_eq rfl),
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC7 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 6 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

/--
Layer 3 for `mov word [mem], imm16` (`C7 /0 iw`, `mod ≠ 3`) after any prefix list `pre` the
prefix scan covers that selects operand size 16, including an FS/GS segment override: as
`mov_m_imm32_prefix_step`, with a 16-bit immediate and `len = pre.length + 4 + am.tail.length`.
-/
theorem mov_m16_imm16_prefix_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 16)
    (hcode : BytesAt s s.RIP (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)))
    (hlow : s.RIP.toNat + (pre.length + 4 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 4 + am.tail.length))) 2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 4 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand 16) (movSpec (imm.signExtend 16))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C7_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xC7 0 am hv (immBytes 16 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 16 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC7 (am.modrm 0) am.tail imm) (by rw [hlen']; omega)
    (by omega)
  rw [show pre.length + 3 + am.tail.length + 16 / 8 = pre.length + 4 + am.tail.length + 1 by
    omega] at hfetch
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 2#64) =
        .ok (am.addrAt s (pre.length + 4 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 2 + am.tail.length + 2 = pre.length + 4 + am.tail.length by omega]
    exact hrip
  rw [mov_m_imm16_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ imm hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hw.of_external_eq rfl),
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 2 = pre.length + 4 + am.tail.length by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC7 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 4 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

/--
Layer 3 for `mov byte [mem], imm8` (`C6 /0 ib`, `mod ≠ 3`) after any prefix list `pre` the prefix
scan covers, including an FS/GS segment override: as `mov_m_imm32_prefix_step`, with an 8-bit
immediate and `len = pre.length + 3 + am.tail.length`.
-/
theorem mov_m8_imm8_prefix_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 64)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length))) 1) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt s (pre.length + 3 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand 8) (movSpec (imm.signExtend 8))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C6_memory_at s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea_seg s h pre 0xC6 0 am hv (immBytes 8 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC6 (am.modrm 0) am.tail imm) (by rw [hlen']; omega)
    (by omega)
  rw [show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by
    omega] at hfetch
  have hrip := handleRIPRelativeAddress_addrMode_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 64 am.isRip (am.offset (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega]
    exact hrip
  rw [mov_m8_imm8_form _ _ _ _ _ _ _ haddr hlock _ _ _ _ _ imm hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hw.of_external_eq rfl),
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC6 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

/-- `mov_m_imm32_prefix_step` at address size 32 (a `67` prefix in `pre`): the store is at
`segAddr ctx (am.addrAt32 s len)` (`AddrMode.addr32`). -/
theorem mov_m_imm32_prefix_a32_step [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 4) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = n)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)))
    (hlow : s.RIP.toNat + (pre.length + 6 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 6 + am.tail.length))) (n / 8)) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 6 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 6 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand n) (movSpec (imm.signExtend n))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length =
      pre.length + 6 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C7_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xC7 0 am hv (immBytes 32 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 32 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 32 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC7 (am.modrm 0) am.tail imm) (by rw [hlen']; omega)
    (by omega)
  rw [show pre.length + 3 + am.tail.length + 32 / 8 = pre.length + 6 + am.tail.length + 1 by
    omega] at hfetch
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 6 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 4#64) =
        .ok (am.addrAt32 s (pre.length + 6 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by omega]
    exact hrip
  rw [mov_m_imm32_form _ _ _ _ _ _ _ n hn hsize haddr hlock _ _ _ _ _ imm hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hw.of_external_eq rfl),
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 4 = pre.length + 6 + am.tail.length by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC7 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 6 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

/-- `mov_m16_imm16_prefix_step` at address size 32 (a `67` prefix in `pre`): the store is at
`segAddr ctx (am.addrAt32 s len)` (`AddrMode.addr32`). -/
theorem mov_m16_imm16_prefix_a32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 6)
    (hsize : (scanContext s.DS (PrefixSegments.ofState s) pre).operand_size = 16)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 16)
    (hcode : BytesAt s s.RIP (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)))
    (hlow : s.RIP.toNat + (pre.length + 4 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 4 + am.tail.length))) 2) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 4 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 4 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand 16) (movSpec (imm.signExtend 16))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)).length =
      pre.length + 4 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C7_memory s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xC7 0 am hv (immBytes 16 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC7 :: am.modrm 0 :: (am.tail ++ immBytes 16 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 16 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC7 (am.modrm 0) am.tail imm) (by rw [hlen']; omega)
    (by omega)
  rw [show pre.length + 3 + am.tail.length + 16 / 8 = pre.length + 4 + am.tail.length + 1 by
    omega] at hfetch
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 4 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 2#64) =
        .ok (am.addrAt32 s (pre.length + 4 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 2 + am.tail.length + 2 = pre.length + 4 + am.tail.length by omega]
    exact hrip
  rw [mov_m_imm16_form _ _ _ _ _ _ _ hsize haddr hlock _ _ _ _ _ imm hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hw.of_external_eq rfl),
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 2 = pre.length + 4 + am.tail.length by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC7 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 4 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

/-- `mov_m8_imm8_prefix_step` at address size 32 (a `67` prefix in `pre`): the store is at
`segAddr ctx (am.addrAt32 s len)` (`AddrMode.addr32`). -/
theorem mov_m8_imm8_prefix_a32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (pre : List UInt8) (hpre : ∀ p ∈ pre, ScanPrefix p) (hlen : pre.length ≤ 7)
    (haddr : (scanContext s.DS (PrefixSegments.ofState s) pre).address_size = 32)
    (hrex2 : (scanContext s.DS (PrefixSegments.ofState s) pre).rex2_prefix_present = false)
    (hlock : (scanContext s.DS (PrefixSegments.ofState s) pre).lock_prefix_present = false)
    (am : AddrMode) (hv : am.Valid)
    (hctx : SegAddrContext (scanContext s.DS (PrefixSegments.ofState s) pre) am) (imm : BitVec 8)
    (hcode : BytesAt s s.RIP (pre ++ 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)))
    (hlow : s.RIP.toNat + (pre.length + 3 + am.tail.length) ≤ 2^32)
    (hw : MemWritable s (segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 3 + am.tail.length))) 1) :
    let addr := segAddr (scanContext s.DS (PrefixSegments.ofState s) pre)
      (am.addrAt32 s (pre.length + 3 + am.tail.length))
    X86.Machine.step s = some (.next (afterStep s (pre.length + 3 + am.tail.length) fun t =>
      writeResult (dataAccess t "store") (.mem addr : Operand 8) (movSpec (imm.signExtend 8))
        (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length))))) := by
  intro addr
  have h5 := am.tail_length_le
  have hlen' : (pre ++ 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length =
      pre.length + 3 + am.tail.length := by simp; omega
  have hlow' : s.RIP.toNat +
      (pre ++ 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)).length ≤ 2^32 := by
    rw [hlen']; exact hlow
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hdecode := decodeLegacy0_run_of_C6_memory_at s h _ pre.length (am.modrm 0)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) (AddrMode.modrmReg_modrm _ _) hcode
    hlow' (getElem?_pre_op _ _ _ _) (getElem?_pre_modrm _ _ _ _) (by omega) _ hrex2
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hea := memAlu_ea32_seg s h pre 0xC6 0 am hv (immBytes 8 imm) _ hctx hcode hlow' (by omega)
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP
      (pre ++ 0xC6 :: am.modrm 0 :: (am.tail ++ immBytes 8 imm)) := hcode
  have hfetch := memFetch_run_of_bytesAt_imm (beforeFetch s) (pre.length + 3 + am.tail.length)
    h.fetchReady hc hlow' 8 (by decide) imm (pre.length + 2 + am.tail.length)
    (getElem?_pre_imm pre 0xC6 (am.modrm 0) am.tail imm) (by rw [hlen']; omega)
    (by omega)
  rw [show pre.length + 3 + am.tail.length + 8 / 8 = pre.length + 3 + am.tail.length + 1 by
    omega] at hfetch
  have hrip := handleRIPRelativeAddress_addrMode32_run am (beforeFetch s)
    (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3 + am.tail.length)))
  rw [AddrMode.addr32_of_gpr rfl] at hrip
  have hrip' : Handle_RIP_Relative_Address 32 am.isRip (am.offset32 (beforeFetch s))
      (BitVec.add (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 2 + am.tail.length))) 1#64) =
        .ok (am.addrAt32 s (pre.length + 3 + am.tail.length)) := by
    rw [add_ofNat_add,
      show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega]
    exact hrip
  rw [mov_m8_imm8_form _ _ _ _ _ _ _ haddr hlock _ _ _ _ _ imm hea hfetch hrip' _
    (SegAccess.ctx hctx.seg am.isStack _) (memAlu_dataReady h _) (hw.of_external_eq rfl),
    add_ofNat_add,
    show pre.length + 2 + am.tail.length + 1 = pre.length + 3 + am.tail.length by omega] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_scan_legacy0 s _ h pre 0xC6 _ hpre (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    (by omega) hcode hlow' hdecode
    ((hmode (pre.length + 3 + am.tail.length + 1)).of_cs_lma_eq rfl rfl)

end X86Proofs
