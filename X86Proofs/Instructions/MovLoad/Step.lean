import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.MemOperand
import X86Proofs.Program.ReadWrite.Load
import X86Proofs.Instructions.MovLoad.Decode
import X86Proofs.Instructions.MovLoad.Form

/-!
# Layer 3: `mov r, [mem]` step theorems

`REX 8B /r` with a memory operand given by an `AddrMode` (any of its shapes: `[base + disp]`,
`[base + index * 2^scale + disp]`, `[rip + disp32]`), the instruction `rex, 8B, am.modrm reg,
am.tail`, `3 + am.tail.length` bytes long:

- `mov_r64_m64_step`: REX.W, a 64-bit load into any of the 16 registers.
- `mov_r32_m32_step`: REX with W = 0, a 32-bit load, zero-extended.

The result is `afterStep s len fun t => writeResult (dataAccess t "load") dst v (RIP + len)` with `v`
the `n / 8` bytes at `AddrMode.addrAt`, read in the state the form starts from (memory is that of `s`).
Preservation: `ReadyToStep.afterStep_load` (`Program/ReadWrite/Load.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem getElem?_cons3 (a b c : UInt8) (l : List UInt8) (j : Nat) :
    (a :: b :: c :: l)[3 + j]? = l[j]? := by
  rw [show 3 + j = j + 1 + 1 + 1 by omega]
  rfl

/-- The common part of the 64- and 32-bit step theorems. -/
theorem mov_rex_8B_memory_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexPrefix rex.toBitVec) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : (rexContext s.DS rex.toBitVec).operand_size = n) (reg : BitVec 3)
    (am : AddrMode) (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX)
    (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x8B :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (3 + am.tail.length)) (n / 8)) :
    let dst : Operand n := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movSpec ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand n).read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) := by
  intro dst
  have hlow' : s.RIP.toNat + (rex :: 0x8B :: am.modrm reg :: am.tail).length ≤ 2^32 := by
    simp only [List.length_cons]; omega
  have hdecode := decodeLegacy0_run_of_rex_8B_memory s h rex (am.modrm reg)
    (by rw [AddrMode.modrmMod_modrm]; exact am.mod_ne_three) am.tail hcode hlow'
  simp only [AddrMode.modrmMod_modrm, AddrMode.modrmReg_modrm, AddrMode.modrmRm_modrm] at hdecode
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (rex :: 0x8B :: am.modrm reg :: am.tail) :=
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
  rw [mov_r_m_form _ t _ _ _ _ _ n hn hsize rfl rfl _ _ _ _ _ hea hrip _ (SegAccess.flat _ _) ht
    hmode hread.low hread.mem] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x8B _ hrex (legacyOpcode_of_check _ ⟨by decide, by decide⟩)
    hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 3 for `mov r64, [mem]` (`REX.W 8B /r`, `mod ≠ 3`), for any destination of the 16 registers
and any addressing shape `am` (REX.X and REX.B as `am` needs). If the machine is ready to step,
the instruction is at RIP below 4 GiB, and the 8 bytes at `am.addrAt s (3 + am.tail.length)` lie below 4 GiB and
are present in RAM (they may cross a page), one `step` loads them into the `reg` register (extended
by REX.R), with `Next_IP` = RIP + `3 + am.tail.length`.
-/
theorem mov_r64_m64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x8B :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (3 + am.tail.length)) 8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movSpec ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 64).read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  mov_rex_8B_memory_step s h rex hrex.rexPrefix 64 (.inl rfl) (hrex.operand_size s.DS) reg am hv
    hx hb hcode hlow hread

/--
Layer 3 for `mov r32, [mem]` (`REX 8B /r` with W = 0, `mod ≠ 3`): as `mov_r64_m64_step`, reading
4 bytes; the 32-bit value is written zero-extended.
-/
theorem mov_r32_m32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (hcode : BytesAt s s.RIP (rex :: 0x8B :: am.modrm reg :: am.tail))
    (hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32)
    (hread : MemReadable s (am.addrAt s (3 + am.tail.length)) 4) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) reg)
    X86.Machine.step s = some (.next (afterStep s (3 + am.tail.length) fun t =>
      writeResult (dataAccess t "load") dst
        (movSpec ((Operand.mem (am.addrAt s (3 + am.tail.length)) : Operand 32).read t))
        (BitVec.add s.RIP (BitVec.ofNat 64 (3 + am.tail.length))))) :=
  mov_rex_8B_memory_step s h rex hrex.rexPrefix 32 (.inr rfl) (hrex.operand_size s.DS) reg am hv
    hx hb hcode hlow hread

end X86Proofs
