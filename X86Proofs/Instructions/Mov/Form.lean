import X86Proofs.Core.Operand
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Mov.Operation

/-!
# Layer 2: MOV register forms

- `mov_r_r_form`: `MOV_GPRv_GPRv_89` (`89 /r`, `mod = 3`), register to register;
  `mov_r16_r16_form` the same at 16 bits.
- `mov_r_imm_form`: `MOV_GPRv_IMMv` (`B8+r`), an immediate of the operand size into the register
  in the opcode's low three bits.
- `mov_r16_imm16_form`: the same at operand size 16 (`66 B8+r iw`).
- `mov_r_imm32_form`: `MOV_GPRv_IMMz` (`C7 /0`, `mod = 3`), a 32-bit immediate, sign-extended to the
  operand size.
- `mov_r16_imm16_c7_form`: the same at operand size 16 (`66 C7 /0 iw`).

The 16-bit ones are used by the generated `mov_imm` rows (`Generated/R16Imm16`, `Generated/RImmC7`):
this file is the one place that unfolds `MOV_GPRv_IMMv` and `MOV_GPRv_IMMz` (architecture rule 5).

Each form ends in `writeResult`: MOV sets no flags and uses no oracle bits (besides the immediate
fetch's, which the caller's fetch lemma accounts for). A 32-bit result is written zero-extended.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `MOV_GPRv_GPRv_89` (`89 /r`, `mod = 3`) at operand size `n` (64 or 32), for any
registers. In 64-bit mode, with operand size `n` and no LOCK prefix, the form succeeds and equals:
read the `reg` (source) register at `n` bits and write it to the `rm` (destination) register, with
`Next_IP := ip`.
-/
theorem mov_r_r_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOV_GPRv_GPRv_89 ip ctx reg rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult s dst (movSpec (src.read s)) ip) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_GPRv_GPRv_89
    simp only [Operand.read_reg64, writeResult, Operand.write_reg64]
    spec_run [
      Read_GPR => readGPR64_run _ _ hmode,
      Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_GPRv_GPRv_89
    simp only [Operand.read_reg32, writeResult, Operand.write_reg32]
    spec_run [
      Read_GPR => readGPR32_run _ _ hmode,
      Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

/--
Layer 2 for `MOV_GPRv_GPRv_89` at operand size 16 (`66 89 /r`, `mod = 3`): as `mov_r_r_form`, the
low 16 bits of the `reg` register written to the `rm` register, its bits above kept (`writeResult`
of a 16-bit register operand). The generated `Instructions/Mov/Generated/RR16` uses it.
-/
theorem mov_r16_r16_form {σ : Type} [X86.Machine.PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (reg rm : BitVec 3) (hmode : In64BitMode s)
    (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.MOV_GPRv_GPRv_89 ip ctx reg rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult s dst (movSpec (src.read s)) ip) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOV_GPRv_GPRv_89
  simp only [Operand.read_reg16, writeResult, Operand.write_reg16]
  spec_run [
    Read_GPR => readGPR16_run _ _ hmode,
    Write_GPR => writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

/--
Layer 2 for `MOV_GPRv_IMMv` (`B8+r`, the register in the opcode's low three bits) at operand size
`n` (64 or 32). In 64-bit mode, with operand size `n` and no LOCK prefix, if fetching `n` bits at
`ip` returns `imm` and leaves state `t` (in 64-bit mode), the form succeeds and equals: write
`imm` to register `opcode[2:0]` (extended by REX.B), with `Next_IP := ip + n / 8`.
-/
theorem mov_r_imm_form [Bindings] (s t : RamState)
    (ip : BitVec 64) (ctx : Instruction_Context) (opcode : BitVec 8) (n : Nat)
    (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n) (hlock : ctx.lock_prefix_present = false)
    (imm : BitVec n) (hfetch : (Mem_Fetch ip n).run s = (.ok imm, t)) (hmode : In64BitMode t) :
    (X86.Instructions.MOV_GPRv_IMMv ip ctx opcode).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))
      (.ok (), writeResult t dst (movSpec imm) (BitVec.add ip (BitVec.ofNat 64 (n / 8)))) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_GPRv_IMMv
    simp only [writeResult, Operand.write_reg64]
    spec_run [
      Mem_Fetch => hfetch]
    dsimp only
    have hv : BitVec.ofInt (Int.toNat 64) imm.toInt = imm := BitVec.ofInt_toInt
    rw [hv]
    exact writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_GPRv_IMMv
    simp only [writeResult, Operand.write_reg32]
    spec_run [
      Mem_Fetch => hfetch]
    dsimp only
    have hv : BitVec.ofInt (Int.toNat 32) imm.toInt = imm := BitVec.ofInt_toInt
    rw [hv]
    exact writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 2 for `MOV_GPRv_IMMv` (`66 B8+r iw`) at operand size 16: as `mov_r_imm_form`, with a 16-bit
immediate written to the low 16 bits of the register (the rest kept) and `Next_IP := ip + 2`.
-/
theorem mov_r16_imm16_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (opcode : BitVec 8) (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) (imm : BitVec 16)
    (hfetch : (Mem_Fetch ip 16).run s = (.ok imm, t)) (hmode : In64BitMode t) :
    (X86.Instructions.MOV_GPRv_IMMv ip ctx opcode).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (opcode.extractLsb' 0 3))
      (.ok (), writeResult t dst (movSpec imm) (BitVec.add ip 2#64)) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOV_GPRv_IMMv
  simp only [writeResult, Operand.write_reg16]
  spec_run [
    Mem_Fetch => hfetch]
  dsimp only
  have hv : BitVec.ofInt (Int.toNat 16) imm.toInt = imm := BitVec.ofInt_toInt
  rw [hv]
  exact writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 2 for `MOV_GPRv_IMMz` (`C7 /0`, `mod = 3`) at operand size `n` (64 or 32). In 64-bit mode,
with operand size `n` and no LOCK prefix, if fetching 32 bits at `ip` returns `imm` and leaves
state `t` (in 64-bit mode), the form succeeds and equals: write `imm` sign-extended to `n` bits to
the `rm` register (extended by REX.B), with `Next_IP := ip + 4`.
-/
theorem mov_r_imm32_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32) (hsize : ctx.operand_size = n)
    (hlock : ctx.lock_prefix_present = false) (imm : BitVec 32)
    (hfetch : (Mem_Fetch ip 32).run s = (.ok imm, t)) (hmode : In64BitMode t) :
    (X86.Instructions.MOV_GPRv_IMMz ip ctx rm).run s =
      let dst : Operand n := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult t dst (movSpec (imm.signExtend n)) (BitVec.add ip 4#64)) := by
  rcases hn with rfl | rfl
  · have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_GPRv_IMMz
    simp only [writeResult, Operand.write_reg64]
    spec_run [
      Mem_Fetch => hfetch]
    dsimp only
    exact writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)
  · have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    unfold X86.Instructions.MOV_GPRv_IMMz
    simp only [writeResult, Operand.write_reg32]
    spec_run [
      Mem_Fetch => hfetch]
    dsimp only
    exact writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)

/--
Layer 2 for `MOV_GPRv_IMMz` (`66 C7 /0 iw`, `mod = 3`) at operand size 16: as `mov_r_imm32_form`,
with a 16-bit immediate (sign-extended to 16 bits, unchanged) written to the low 16 bits of the
`rm` register (the rest kept) and `Next_IP := ip + 2`.
-/
theorem mov_r16_imm16_c7_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (rm : BitVec 3) (hsize : ctx.operand_size = 16)
    (hlock : ctx.lock_prefix_present = false) (imm : BitVec 16)
    (hfetch : (Mem_Fetch ip 16).run s = (.ok imm, t)) (hmode : In64BitMode t) :
    (X86.Instructions.MOV_GPRv_IMMz ip ctx rm).run s =
      let dst : Operand 16 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 rm)
      (.ok (), writeResult t dst (movSpec (imm.signExtend 16)) (BitVec.add ip 2#64)) := by
  have hcontext : {ctx with operand_size := 16, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.MOV_GPRv_IMMz
  simp only [writeResult, Operand.write_reg16]
  spec_run [
    Mem_Fetch => hfetch]
  dsimp only
  exact writeGPR16_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)

end X86Proofs
