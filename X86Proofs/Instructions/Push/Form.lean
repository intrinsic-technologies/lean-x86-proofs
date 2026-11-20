import X86Proofs.Program.ReadWrite.Stack

/-!
# Layer 2: PUSH r64

- `push_r_form`: `PUSH_GPRv_50_0` (`50+r`, the register in the opcode's low three bits,
  extended by REX.B) at 64 bits: read the register, then `Operations.PUSH 64` (`push_operation`).

In 64-bit mode the operand size of `50+r` is 64 unless a `66` prefix makes it 16; REX.W does not
matter (lean-x86 computes the size from `rex_w` and the `66` prefix, not from the context's
`operand_size`), so the form lemma asks for no `66` prefix only.

- `push_r16_form`: the same with a `66` prefix and REX.W clear (operand size 16): push the low 16
  bits of the register (`push16_operation`), for the generated `Instructions/Push/Generated/R16`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `PUSH_GPRv_50_0` at 64 bits. In 64-bit mode, with no `66` and no LOCK prefix, on a
state ready for data accesses with the flat stack segment and the 8 bytes at RSP - 8 writable in
place, the form succeeds and equals: read register `opcode[2:0]` (extended by REX.B), set
`Next_IP := ip`, and push the value (`pushState`).
-/
theorem push_r_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (opcode : BitVec 8) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hw : MemWritable t (pushAddr t) 8) :
    (X86.Instructions.PUSH_GPRv_50_0 ip ctx opcode).run t =
      let src : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))
      (.ok (), pushState { t with Next_IP := ip } (src.read t)) := by
  have hpush := push_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
  simp only [Operand.read_reg64]
  -- The operand size is `if rex_w == 1 then 64 else …`: split on REX.W so that it evaluates.
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = w
  rcases hw1 w with rfl | rfl <;>
  · unfold X86.Instructions.PUSH_GPRv_50_0
    spec_run [Read_GPR => readGPR64_run _ _ hmode,
      X86.Instructions.Operations.PUSH => hpush _ (hw.of_external_eq rfl)]

/--
Layer 2 for `PUSH_GPRv_50_0` at 16 bits (`66 50+r`, REX.W clear). As `push_r_form`, with the low 16
bits of the register pushed at RSP - 2 (`pushState16`).
-/
theorem push_r16_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (opcode : BitVec 8) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = true)
    (hw0 : ctx.rex_w = 0) (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hw : MemWritable t (pushAddr16 t) 2) :
    (X86.Instructions.PUSH_GPRv_50_0 ip ctx opcode).run t =
      let src : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))
      (.ok (), pushState16 { t with Next_IP := ip } (src.read t)) := by
  have hpush := push16_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
  simp only [Operand.read_reg16]
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := true, lock_prefix_present := false,
      rex_w := 0 } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.PUSH_GPRv_50_0
  spec_run [Read_GPR => readGPR16_run _ _ hmode,
    X86.Instructions.Operations.PUSH => hpush _ (hw.of_external_eq rfl)]

end X86Proofs
