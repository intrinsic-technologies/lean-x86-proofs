import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Lea.Operation

/-!
# Layer 2: `LEA_GPRv_AGEN` (`8D /r`)

`lea r, [mem]` at operand size 64: compute the address (`Effective_Address`, then
`Handle_RIP_Relative_Address`), set `Next_IP`, and write the address to the `reg` register. The
segment `Effective_Address` returns is dropped: LEA reads no memory and translates nothing, so
there is no memory precondition. No flags change (`writeResult`).

As for `mov_r_m_form`, the form lemma takes the address computation as a hypothesis (`hea`,
`hrip`), so it holds for every addressing shape.

- `lea_r32_m_form`, `lea_r16_m_form`: the same at operand size 32 and 16, the result the address's
  low bits (`leaSpec`, `lea_operation`), zero-extended (32) or merged into the register (16). The
  generated `Instructions/Lea/Generated/RM` uses them.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `LEA_GPRv_AGEN` (`8D /r`, `mod ≠ 3`) at operand size 64. In 64-bit mode, at
address size `asz` (64, or 32 after a `67` prefix) and with no LOCK prefix: if the address
computation returns offset `off` and the address after the displacement `next` and leaves state
`t`, and RIP-relative handling gives `addr`, the form succeeds and equals: set
`Next_IP := next` and write `addr` to the `reg` register.
-/
theorem lea_r_m_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 64)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (hmode : In64BitMode t) :
    (X86.Instructions.LEA_GPRv_AGEN ip ctx mod reg rm).run s =
      (.ok (), writeResult t (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 64) addr
        next) := by
  have hcontext :
      {ctx with operand_size := 64, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.LEA_GPRv_AGEN
  simp only [writeResult, Operand.write_reg64]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [MonadState.get => get_run _]
  refine (writeGPR64_run _ _ _ (hmode.of_cs_lma_eq (t := {t with Next_IP := next}) rfl rfl)).trans ?_
  have hx : ∀ x : BitVec 64, BitVec.extractLsb' (Int.toNat 0) (Int.toNat 64) x = x := fun x => by
    simp
  simp only [hx]
  rfl

/--
Layer 2 for `LEA_GPRv_AGEN` at operand size 32 (`8D /r`, `mod ≠ 3`, no `66`, no REX.W): as
`lea_r_m_form`, with the address's low 32 bits (`leaSpec 32`) written to the `reg` register,
zero-extended.
-/
theorem lea_r32_m_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3) (hsize : ctx.operand_size = 32)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (hmode : In64BitMode t) :
    (X86.Instructions.LEA_GPRv_AGEN ip ctx mod reg rm).run s =
      (.ok (), writeResult t (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32)
        (leaSpec 32 addr) next) := by
  have hcontext :
      {ctx with operand_size := 32, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.LEA_GPRv_AGEN
  simp only [writeResult, Operand.write_reg32]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [MonadState.get => get_run _,
    X86.Instructions.Operations.LEA => lea_operation _ 32 (.inr (.inl rfl)) _,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

/--
Layer 2 for `LEA_GPRv_AGEN` at operand size 16 (`66 8D /r`, `mod ≠ 3`): as `lea_r_m_form`, with
the address's low 16 bits (`leaSpec 16`) written to the low 16 bits of the `reg` register, its bits
above kept.
-/
theorem lea_r16_m_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3) (hsize : ctx.operand_size = 16)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (hmode : In64BitMode t) :
    (X86.Instructions.LEA_GPRv_AGEN ip ctx mod reg rm).run s =
      (.ok (), writeResult t (.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 16)
        (leaSpec 16 addr) next) := by
  have hcontext :
      {ctx with operand_size := 16, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.LEA_GPRv_AGEN
  simp only [writeResult, Operand.write_reg16]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [MonadState.get => get_run _,
    X86.Instructions.Operations.LEA => lea_operation _ 16 (.inr (.inr rfl)) _,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
