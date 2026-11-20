import X86Proofs.Step.AfterStep
import X86Proofs.Step.LegacyStep
import X86Proofs.Step.FetchImm
import X86Proofs.Instructions.Mov.Decode
import X86Proofs.Instructions.Mov.Form

/-!
# Layer 3: MOV step theorems

One step theorem and one preservation theorem per encoding:

`mov r/m, r` (`89 /r`, both operands registers):
- `mov_r64_r64_step`: `REX.W 89 /r`, 64-bit, any two of the 16 registers.
- `mov_r32_r32_step`: `89 /r` with no prefix, 32-bit, registers 0–7.
- `mov_r32_r32_rex_step`: `REX 89 /r` with W = 0, 32-bit, any two of the 16 registers.

`mov r, imm` (`B8+r`, the register in the opcode's low three bits):
- `mov_r32_imm32_step`: `B8+r imm32` with no prefix, registers 0–7.
- `mov_r32_imm32_rex_step`: `REX B8+r imm32` with W = 0, any of the 16 registers.
- `mov_r64_imm64_step`: `REX.W B8+r imm64`, any of the 16 registers.

`mov r/m64, imm32` (`C7 /0`, `mod = 3`):
- `mov_r64_imm32_step`: `REX.W C7 /0 imm32`, the immediate sign-extended, any of the 16 registers.

The immediate is stored in the instruction as its little-endian bytes (`immBytes`); a 32-bit
result is written zero-extended.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-! ### `89 /r` -/

/--
Layer 3 for `mov r/m64, r64` with both operands registers (`REX.W 89 /r`, `mod = 3`), for any two
of the 16 registers. If the machine is ready to step and the bytes at RIP, below 4 GiB, are a REX
prefix with W = 1, opcode `89` and a ModRM byte with `mod = 3`, then one `step` runs normally and
its result is the layer-2 result (`writeResult` of the `reg` register into the `rm` register at
64 bits, extended by REX.R and REX.B) with `Next_IP` = RIP + 3, plus the per-step housekeeping.
-/
theorem mov_r64_r64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x89, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t dst (movSpec (src.read t)) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_89 s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [mov_r_r_form _ _ _ _ _ hmode 64 (by decide) (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x89 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

/-- Preservation for `mov_r64_r64_step`: the state after the step is ready to step again. -/
theorem mov_r64_r64_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 64 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeResult t dst (movSpec (src.read t)) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeResult h 3 _ _ _

/--
Layer 3 for `mov r/m32, r32` with both operands registers (`89 /r` with no prefix, `mod = 3`),
for any two of the registers 0–7: as `mov_r64_r64_step`, at 32 bits, with `Next_IP` = RIP + 2.
The 32-bit value is written zero-extended.
-/
theorem mov_r32_r32_step [Bindings] (s : RamState) (h : ReadyToStep s) (modrm : UInt8)
    (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x89, modrm]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    let src : Operand 32 := .reg (gprNumber 0 0 (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeResult t dst (movSpec (src.read t)) (BitVec.add s.RIP 2#64))) := by
  have hdecode := decodeLegacy0_run_of_89 s h modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [mov_r_r_form _ _ _ _ _ hmode 32 (by decide) (legacyContext_operand_size s.DS) rfl]
    at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h 0x89 [modrm]
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

/-- Preservation for `mov_r32_r32_step`. -/
theorem mov_r32_r32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (modrmRm modrm))
    let src : Operand 32 := .reg (gprNumber 0 0 (modrmReg modrm))
    ReadyToStep (afterStep s 2 fun t =>
      writeResult t dst (movSpec (src.read t)) (BitVec.add s.RIP 2#64)) :=
  ReadyToStep.afterStep_writeResult h 2 _ _ _

/--
Layer 3 for `mov r/m32, r32` with both operands registers (`REX 89 /r` with W = 0, `mod = 3`),
for any two of the 16 registers: as `mov_r64_r64_step`, at 32 bits. The 32-bit value is written
zero-extended.
-/
theorem mov_r32_r32_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x89, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t dst (movSpec (src.read t)) (BitVec.add s.RIP 3#64))) := by
  have hdecode := decodeLegacy0_run_of_rex_89 s h rex modrm hmod hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [mov_r_r_form _ _ _ _ _ hmode 32 (by decide) (hrex.operand_size s.DS) rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0x89 [modrm] hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow hdecode (hmode.of_cs_lma_eq rfl rfl)

/-- Preservation for `mov_r32_r32_rex_step`. -/
theorem mov_r32_r32_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    let src : Operand 32 := .reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    ReadyToStep (afterStep s 3 fun t =>
      writeResult t dst (movSpec (src.read t)) (BitVec.add s.RIP 3#64)) :=
  ReadyToStep.afterStep_writeResult h 3 _ _ _

/-! ### `B8+r` -/

/--
Layer 3 for `mov r32, imm32` (`B8+r imm32` with no prefix), for any of the registers 0–7. If the
machine is ready to step and the bytes at RIP, below 4 GiB, are an opcode `B8`–`BF` and the four
bytes of `imm`, then one `step` runs normally and its result is the layer-2 result (`writeResult`
of `imm` into register `op & 7`, zero-extended) with `Next_IP` = RIP + 5, plus the per-step
housekeeping.
-/
theorem mov_r32_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s) (op : UInt8)
    (hop : MovImmOpcode op) (imm : BitVec 32) (hcode : BytesAt s s.RIP (op :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 5 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 5 fun t =>
      writeResult t dst (movSpec imm) (BitVec.add s.RIP 5#64))) := by
  have hlow' : s.RIP.toNat + (op :: immBytes 32 imm).length ≤ 2^32 := by simpa using hlow
  have hdecode := decodeLegacy0_run_of_movImm s h op hop _ hcode hlow'
  have hfetch := memFetch_run_of_bytesAt_imm32 (beforeFetch s) 2 h.fetchReady hcode hlow' imm 1
    (immBytes_getElem?_append [op] imm) (by simp) (by decide)
  have hmode : In64BitMode (afterFetches (beforeFetch s) 6) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [mov_r_imm_form _ _ (BitVec.add s.RIP 1#64) _ _ 32 (by decide)
    (legacyContext_operand_size s.DS) rfl imm hfetch hmode,
    show BitVec.add (BitVec.add s.RIP 1#64) (BitVec.ofNat 64 (32 / 8)) = BitVec.add s.RIP 5#64
      from BitVec.add_assoc s.RIP 1#64 4#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy0 s _ h op _ hop.legacyOpcode hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

/-- Preservation for `mov_r32_imm32_step`. -/
theorem mov_r32_imm32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (op : UInt8)
    (imm : BitVec 32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (opcodeReg op))
    ReadyToStep (afterStep s 5 fun t => writeResult t dst (movSpec imm) (BitVec.add s.RIP 5#64)) :=
  ReadyToStep.afterStep_writeResult h 5 _ _ _

/--
Layer 3 for `mov r32, imm32` (`REX B8+r imm32` with W = 0), for any of the 16 registers: as
`mov_r32_imm32_step`, with the register extended by REX.B and `Next_IP` = RIP + 6.
-/
theorem mov_r32_imm32_rex_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex op : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hop : MovImmOpcode op) (imm : BitVec 32)
    (hcode : BytesAt s s.RIP (rex :: op :: immBytes 32 imm)) (hlow : s.RIP.toNat + 6 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 6 fun t =>
      writeResult t dst (movSpec imm) (BitVec.add s.RIP 6#64))) := by
  have hlow' : s.RIP.toNat + (rex :: op :: immBytes 32 imm).length ≤ 2^32 := by simpa using hlow
  have hdecode := decodeLegacy0_run_of_rex_movImm s h rex op hop _ hcode hlow'
  have hfetch := memFetch_run_of_bytesAt_imm32 (beforeFetch s) 3 h.fetchReady hcode hlow' imm 2
    (immBytes_getElem?_append [rex, op] imm) (by simp) (by decide)
  have hmode : In64BitMode (afterFetches (beforeFetch s) 7) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [mov_r_imm_form _ _ (BitVec.add s.RIP 2#64) _ _ 32 (by decide)
    (hrex.operand_size s.DS) rfl imm hfetch hmode,
    show BitVec.add (BitVec.add s.RIP 2#64) (BitVec.ofNat 64 (32 / 8)) = BitVec.add s.RIP 6#64
      from BitVec.add_assoc s.RIP 2#64 4#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex op _ hrex.rexPrefix hop.legacyOpcode hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

/-- Preservation for `mov_r32_imm32_rex_step`. -/
theorem mov_r32_imm32_rex_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex op : UInt8)
    (imm : BitVec 32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
    ReadyToStep (afterStep s 6 fun t => writeResult t dst (movSpec imm) (BitVec.add s.RIP 6#64)) :=
  ReadyToStep.afterStep_writeResult h 6 _ _ _

/--
Layer 3 for `mov r64, imm64` (`REX.W B8+r imm64`), for any of the 16 registers: as
`mov_r32_imm32_step`, with an 8-byte immediate, the register extended by REX.B, the full 64-bit
register written and `Next_IP` = RIP + 10.
-/
theorem mov_r64_imm64_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex op : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hop : MovImmOpcode op) (imm : BitVec 64)
    (hcode : BytesAt s s.RIP (rex :: op :: immBytes 64 imm)) (hlow : s.RIP.toNat + 10 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
    X86.Machine.step s = some (.next (afterStep s 10 fun t =>
      writeResult t dst (movSpec imm) (BitVec.add s.RIP 10#64))) := by
  have hlow' : s.RIP.toNat + (rex :: op :: immBytes 64 imm).length ≤ 2^32 := by simpa using hlow
  have hdecode := decodeLegacy0_run_of_rex_movImm s h rex op hop _ hcode hlow'
  have hfetch := memFetch_run_of_bytesAt_imm64 (beforeFetch s) 3 h.fetchReady hcode hlow' imm 2
    (immBytes_getElem?_append [rex, op] imm) (by simp) (by decide)
  have hmode : In64BitMode (afterFetches (beforeFetch s) 11) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [mov_r_imm_form _ _ (BitVec.add s.RIP 2#64) _ _ 64 (by decide)
    (hrex.operand_size s.DS) rfl imm hfetch hmode,
    show BitVec.add (BitVec.add s.RIP 2#64) (BitVec.ofNat 64 (64 / 8)) = BitVec.add s.RIP 10#64
      from BitVec.add_assoc s.RIP 2#64 8#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex op _ hrex.rexPrefix hop.legacyOpcode hcode hlow' hdecode
    (hmode.of_cs_lma_eq rfl rfl)

/-- Preservation for `mov_r64_imm64_step`. -/
theorem mov_r64_imm64_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex op : UInt8)
    (imm : BitVec 64) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (opcodeReg op))
    ReadyToStep (afterStep s 10 fun t => writeResult t dst (movSpec imm) (BitVec.add s.RIP 10#64)) :=
  ReadyToStep.afterStep_writeResult h 10 _ _ _

/-! ### `C7 /0` -/

/--
Layer 3 for `mov r/m64, imm32` with a register operand (`REX.W C7 /0 imm32`, `mod = 3`), for any
of the 16 registers. If the machine is ready to step and the bytes at RIP, below 4 GiB, are a REX
prefix with W = 1, opcode `C7`, a ModRM byte with `mod = 3` and `reg = 0`, and the four bytes of
`imm`, then one `step` runs normally and its result is the layer-2 result (`writeResult` of `imm`
sign-extended to 64 bits into the `rm` register, extended by REX.B) with `Next_IP` = RIP + 7,
plus the per-step housekeeping.
-/
theorem mov_r64_imm32_step [Bindings] (s : RamState) (h : ReadyToStep s) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (imm : BitVec 32) (hcode : BytesAt s s.RIP (rex :: 0xC7 :: modrm :: immBytes 32 imm))
    (hlow : s.RIP.toNat + 7 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 7 fun t =>
      writeResult t dst (movSpec (imm.signExtend 64)) (BitVec.add s.RIP 7#64))) := by
  have hlow' : s.RIP.toNat + (rex :: 0xC7 :: modrm :: immBytes 32 imm).length ≤ 2^32 := by
    simpa using hlow
  have hdecode := decodeLegacy0_run_of_rex_C7 s h rex modrm hmod hreg _ hcode hlow'
  have hfetch := memFetch_run_of_bytesAt_imm32 (beforeFetch s) 4 h.fetchReady hcode hlow' imm 3
    (immBytes_getElem?_append [rex, 0xC7, modrm] imm) (by simp) (by decide)
  have hmode : In64BitMode (afterFetches (beforeFetch s) 8) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  rw [mov_r_imm32_form _ _ (BitVec.add s.RIP 3#64) _ _ 64 (by decide)
    (hrex.operand_size s.DS) rfl imm hfetch hmode,
    show BitVec.add (BitVec.add s.RIP 3#64) 4#64 = BitVec.add s.RIP 7#64
      from BitVec.add_assoc s.RIP 3#64 4#64] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy0 s _ h rex 0xC7 _ hrex.rexPrefix
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow' hdecode (hmode.of_cs_lma_eq rfl rfl)

/-- Preservation for `mov_r64_imm32_step`. -/
theorem mov_r64_imm32_ready [Bindings] {s : RamState} (h : ReadyToStep s) (rex modrm : UInt8)
    (imm : BitVec 32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    ReadyToStep (afterStep s 7 fun t =>
      writeResult t dst (movSpec (imm.signExtend 64)) (BitVec.add s.RIP 7#64)) :=
  ReadyToStep.afterStep_writeResult h 7 _ _ _

end X86Proofs
