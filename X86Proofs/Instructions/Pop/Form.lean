import X86Proofs.Program.ReadWrite.Stack

/-!
# Layer 2: POP r64

- `pop_r_form`: `POP_GPRv_58_0` (`58+r`, the register in the opcode's low three bits,
  extended by REX.B) at 64 bits: set `Next_IP`, `Operations.POP 64` (`pop_operation`: read the 8 bytes
  at RSP), RSP := RSP + 8 (`Write_RSP`), then write the value to the register.

As for `push_r_form`, the operand size of `58+r` in 64-bit mode is 64 unless a `66` prefix
makes it 16; REX.W does not matter, so the form lemma asks for no `66` prefix only.

- `pop_r16_form`: the same with a `66` prefix and REX.W clear (operand size 16): pop 2 bytes into
  the low 16 bits of the register (`pop16_operation`), for the generated
  `Instructions/Pop/Generated/R16`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `POP_GPRv_58_0` at 64 bits. In 64-bit mode, with no `66` and no LOCK prefix, on a
state ready for data accesses with the flat stack segment and the 8 bytes at RSP readable, the
form succeeds and equals: set `Next_IP := ip` and pop into register `opcode[2:0]` (extended by
REX.B) (`popState`).
-/
theorem pop_r_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (opcode : BitVec 8) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 8) :
    (X86.Instructions.POP_GPRv_58_0 ip ctx opcode).run t =
      (.ok (), popState { t with Next_IP := ip }
        (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))) := by
  have hpop := pop_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hr.of_external_eq rfl)
  simp only [popState, Operand.write_reg64]
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
  · unfold X86.Instructions.POP_GPRv_58_0
    spec_run [X86.Instructions.Operations.POP => hpop, Write_RSP => writeRSP64_run _ _]
    refine (writeGPR64_run _ _ _ ?_).trans ?_
    · exact hmode.of_cs_lma_eq rfl rfl
    · simp only [Operand.write_reg64]
      rfl

/--
Layer 2 for `POP_GPRv_58_0` at 16 bits (`66 58+r`, REX.W clear). As `pop_r_form`, popping the 2
bytes at RSP into the low 16 bits of the register (`popState16`).
-/
theorem pop_r16_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (opcode : BitVec 8) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = true)
    (hw0 : ctx.rex_w = 0) (hlock : ctx.lock_prefix_present = false) (hmode : In64BitMode t)
    (h : DataReady t) (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 2) :
    (X86.Instructions.POP_GPRv_58_0 ip ctx opcode).run t =
      (.ok (), popState16 { t with Next_IP := ip }
        (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))) := by
  have hpop := pop16_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables) hss
    (hr.of_external_eq rfl)
  simp only [popState16, Operand.write_reg16]
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := true, lock_prefix_present := false,
      rex_w := 0 } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.POP_GPRv_58_0
  spec_run [X86.Instructions.Operations.POP => hpop, Write_RSP => writeRSP64_run _ _]
  refine (writeGPR16_run _ _ _ ?_).trans ?_
  · exact hmode.of_cs_lma_eq rfl rfl
  · rfl

end X86Proofs
