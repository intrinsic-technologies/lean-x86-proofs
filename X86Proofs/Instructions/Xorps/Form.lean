import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Pxor.Operation

/-!
# Layer 2: `XORPS_XMMxud_XMMxud` (`0F 57 /r`, `mod = 3`)

`xorps xmm, xmm`: read the destination (`reg`) and source (`rm`) XMM registers, pass the prefix
checks (no `F2`/`F3`, LOCK or `66`) and the SSE control-register checks (`CR4.OSFXSR = 1`,
`CR0.EM = 0`, `CR0.TS = 0`, from `Prelude.SupportedSSE`), set `Next_IP`, and write the
128-bit xor to the destination, keeping bits 128–511 of its ZMM register (a legacy SSE write: no
VEX/EVEX prefix). No flags.

- `pxor_operation` (`Instructions/Pxor/Operation.lean`): lean-x86's `PXOR` (XORPS's operation)
  at 128 bits is `^^^`.
- `calculateRM_run_of_mod3`: the `rm` register number with `mod = 3` and no EVEX prefix.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- `Calculate_RM` with `mod = 3` and no EVEX prefix: `rm` extended by REX.B (and REX2's B4). -/
theorem calculateRM_run_of_mod3 (rm : BitVec 3) (ctx : Instruction_Context)
    (hevex : ctx.evex_prefix_present = false) :
    Calculate_RM 3 rm ctx = .ok (gprNumber ctx.rex_b4 ctx.rex_b3 rm) := by
  unfold Calculate_RM
  simp [hevex, HAnd.hAnd, AndOp.and, strictAnd, x86_runtime, bind, pure, Except.bind, Except.pure]
  generalize ctx.rex_x3 = x3
  generalize ctx.rex_b4 = b4
  generalize ctx.rex_b3 = b3
  revert x3 b4 b3 rm
  decide

/--
Layer 2 for `XORPS_XMMxud_XMMxud` (`0F 57 /r`, `mod = 3`), for any registers. In 64-bit mode, with
SSE enabled and no `F2`/`F3`, LOCK, `66`, VEX or EVEX prefix, the form succeeds and equals:
set `Next_IP := ip` and write the destination (`reg`) xor the source (`rm`) to the destination
(`writeResult`; an XMM write keeps bits 128–511 of the ZMM register).
-/
theorem xorps_xmm_xmm_form [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (reg rm : BitVec 3) (hmode : In64BitMode s) (hsse : Prelude.SupportedSSE Bindings.processor s)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) :
    (X86.Instructions.XORPS_XMMxud_XMMxud ip ctx 3 reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      let src : Operand 128 := .xmm (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult s dst (dst.read s ^^^ src.read s) ip) := by
  have hm' : In64BitMode { s with Next_IP := ip } := hmode.of_cs_lma_eq rfl rfl
  unfold X86.Instructions.XORPS_XMMxud_XMMxud
  simp only [hrep, hlock, hosz, hvex, hevex, calculateRM_run_of_mod3 rm ctx hevex]
  spec_run [
    Read_XMM => readXMM128_run _ _ hmode,
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    X86.Instructions.Operations.PXOR => pxor_operation _ _]
  refine (writeXMM128_run _ _ _ hm').trans ?_
  have hnum : ∀ (a b : BitVec 1) (c : BitVec 3), (BitVec.ofNat (2 + 3 : Int).toNat
      ((BitVec.ofNat (1 + 1 : Int).toNat (a.toNat <<< Int.toNat 1 + b.toNat)).toNat <<<
        Int.toNat 3 + c.toNat) : BitVec 5) = gprNumber a b c := fun _ _ _ => rfl
  simp only [writeResult, Operand.write_xmm, Operand.read_xmm, hnum]

end X86Proofs
