import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Mov.Operation

/-!
# Layer 2: `MOV_GPRv_MEMv_1` (`8B /r`, memory operand)

`mov r, [mem]` at operand size 64 or 32 (`mov_r_m_form`) and 16 (`mov_r16_m16_form`): compute
the address (`Effective_Address`, then `Handle_RIP_Relative_Address`), read `n / 8` bytes there
through the operand's segment (`logicalMemRead_run_seg`, which may cross a page: the flat data
segment, or FS or GS after a segment prefix, whose base it adds), set `Next_IP`, and
write the value to the `reg` register (zero-extended at 32 bits, merged at 16).

The form lemma takes the address computation as a hypothesis (`hea`, `hrip`), so it holds for every
addressing shape; `effectiveAddress_run` and `handleRIPRelativeAddress_addrMode_run` discharge it for an `AddrMode`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `MOV_GPRv_MEMv_1` (`8B /r`, `mod ≠ 3`) at operand size `n` (64 or 32). In 64-bit mode,
at address size `asz` (64, or 32 after `67`) and with no LOCK prefix: if the address computation
returns offset `off` through segment `seg` and leaves state `t`, RIP-relative handling gives `addr`,
whose linear address in `seg` is `lin` (`SegAccess`: `addr` itself for a flat segment, `base + addr`
for FS or GS), and the `n / 8` bytes at `lin` lie below 4 GiB and are present in RAM, the form
succeeds and equals: read them (`dataAccess t "load"`: the read's bookkeeping), set `Next_IP :=
next`, and write the value to the `reg` register.
-/
theorem mov_r_m_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + n / 8 ≤ 2^32)
    (hmem : ∀ i, i < n / 8 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOV_GPRv_MEMv_1 ip ctx mod reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst
        (movSpec ((Operand.mem lin : Operand n).read t)) next) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg t ht seg addr lin hseg 64 (by decide) .Memory_Read (.inl rfl)
      hlow hmem
    unfold X86.Instructions.MOV_GPRv_MEMv_1
    simp only [writeResult, Operand.write_reg64]
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext :
        {ctx with operand_size := 32, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hread := logicalMemRead_run_seg t ht seg addr lin hseg 32 (by decide) .Memory_Read (.inl rfl)
      hlow hmem
    unfold X86.Instructions.MOV_GPRv_MEMv_1
    simp only [writeResult, Operand.write_reg32]
    refine (specM_bind_run _ _ hea).trans ?_
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [
      Logical_Mem_Read => hread,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

/--
Layer 2 for `MOV_GPRv_MEMv_1` at operand size 16 (`66 8B /r`, `mod ≠ 3`): as `mov_r_m_form`, the 2
bytes at `addr` written to the low 16 bits of the `reg` register, its bits above kept. The
generated `Instructions/Mov/Generated/RM` uses it.
-/
theorem mov_r16_m16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 16)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t)
    (hlow : lin.toNat + 2 ≤ 2^32)
    (hmem : ∀ i, i < 2 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOV_GPRv_MEMv_1 ip ctx mod reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst
        (movSpec ((Operand.mem lin : Operand 16).read t)) next) := by
  have hcontext :
      {ctx with operand_size := 16, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hread := logicalMemRead_run_seg t ht seg addr lin hseg 16 (by decide) .Memory_Read (.inl rfl) hlow
    hmem
  unfold X86.Instructions.MOV_GPRv_MEMv_1
  simp only [writeResult, Operand.write_reg16]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    Logical_Mem_Read => hread,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

end X86Proofs
