import X86Proofs.Step.AfterStep
import X86Proofs.Program.ReadWrite.Sse
import X86Proofs.Instructions.Xorps.Decode
import X86Proofs.Instructions.Xorps.Form

/-!
# Layer 3: `xorps xmm, xmm` step theorems

`0F 57 /r` with both operands XMM registers (`mod = 3`), optionally after a REX prefix:

- `xorps_xmm_xmm_step`: `0F 57 modrm` (no prefix; e.g. `0F 57 C0`, `xorps xmm0, xmm0`),
  registers 0–7, 3 bytes.
- `xorps_xmm_xmm_rex_step`: `rex 0F 57 modrm`, any of the 16 registers (REX.R, REX.B; REX.W is
  ignored), 4 bytes.

The result is `afterStep s len fun t => writeResult t dst (dst.read t ^^^ src.read t) (RIP + len)`
with `dst` the `reg` register and `src` the `rm` register. Besides `ReadyToStep`, the step needs
SSE enabled (`Prelude.SupportedSSE`, `Step/Sse.lean`). Preservation:
`ReadyToStep.afterStep_writeResult_xmm` (`Program/ReadWrite/Sse.lean`).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 3 for `xorps xmm, xmm` (`0F 57 /r`, no prefix, `mod = 3`), registers 0–7. If the machine is
ready to step with SSE enabled and the bytes `0F 57 modrm` are at RIP below 4 GiB, one `step`
xors the `rm` register into the `reg` register, with `Next_IP` = RIP + 3.
-/
theorem xorps_xmm_xmm_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (modrm : UInt8) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [0x0F, 0x57, modrm]) (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    let dst : Operand 128 := .xmm (gprNumber 0 0 (modrmReg modrm))
    let src : Operand 128 := .xmm (gprNumber 0 0 (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t dst (dst.read t ^^^ src.read t) (BitVec.add s.RIP 3#64))) := by
  intro dst src
  have hdecode := decodeLegacy1_run_of_57_register s h hsse (legacyContext s.DS) rfl rfl modrm hmod
    [0x0F, 0x57, modrm] 1 (by decide) rfl rfl hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hsse' : Prelude.SupportedSSE Bindings.processor (afterFetches (beforeFetch s) 4) :=
    SupportedSSE.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsse
  rw [xorps_xmm_xmm_form _ _ _ _ _ hmode hsse' rfl rfl rfl rfl rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h 0x57 [modrm] ⟨by decide, by decide⟩ hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 3 for `xorps xmm, xmm` after a REX prefix (`rex 0F 57 /r`, `mod = 3`), any of the 16
registers (REX.R extends `reg`, REX.B extends `rm`). As `xorps_xmm_xmm_step` otherwise, with
`Next_IP` = RIP + 4.
-/
theorem xorps_xmm_xmm_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (hsse : Prelude.SupportedSSE Bindings.processor s) (rex modrm : UInt8)
    (hrex : RexPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hcode : BytesAt s s.RIP [rex, 0x0F, 0x57, modrm]) (hlow : s.RIP.toNat + 4 ≤ 2^32) :
    let dst : Operand 128 := .xmm (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm))
    let src : Operand 128 := .xmm (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm))
    X86.Machine.step s = some (.next (afterStep s 4 fun t =>
      writeResult t dst (dst.read t ^^^ src.read t) (BitVec.add s.RIP 4#64))) := by
  intro dst src
  have hdecode := decodeLegacy1_run_of_57_register s h hsse (rexContext s.DS rex.toBitVec) rfl rfl modrm
    hmod [rex, 0x0F, 0x57, modrm] 2 (by decide) rfl rfl hcode hlow
  have hmode : In64BitMode (afterFetches (beforeFetch s) 5) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hsse' : Prelude.SupportedSSE Bindings.processor (afterFetches (beforeFetch s) 5) :=
    SupportedSSE.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsse
  rw [xorps_xmm_xmm_form _ _ _ _ _ hmode hsse' rfl rfl rfl rfl rfl] at hdecode
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex 0x57 [modrm] hrex ⟨by decide, by decide⟩ hcode hlow hdecode
    (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
