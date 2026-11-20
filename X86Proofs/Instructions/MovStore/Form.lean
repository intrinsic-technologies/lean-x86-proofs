import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.Mov.Operation

/-!
# Layer 2: `MOV_MEMv_GPRv_1`, `MOV_MEMv_IMMz_1`, `MOV_MEMb_IMMb_1` (stores)

`mov [mem], r` (`89 /r`), `mov [mem], imm` (`C7 /0 iz`) and `mov [mem], imm8` (`C6 /0 ib`), each
with `mod ≠ 3`: compute the address (`Effective_Address`, then `Handle_RIP_Relative_Address`),
read the source (a register, or an immediate fetched after the displacement), set `Next_IP`, and
write `n / 8` bytes (they may cross a page) through any segment whose linear address for the
offset is known (`logicalMemWrite_run_seg`: the flat data segment, or FS or GS after a segment
prefix).

The result is `writeResult (dataAccess u "store") (.mem addr) v next` (`Program/ReadWrite/Store.lean`). As
for loads, the address computation is a hypothesis (`hea`, `hrip`), so each lemma holds for every
addressing shape. For the immediate forms the RIP-relative base is the address after the
immediate (the end of the instruction).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `MOV_MEMv_GPRv_1` (`89 /r`, `mod ≠ 3`) at operand size `n` (64 or 32). In 64-bit mode,
at address size `asz` (64, or 32 after `67`) and with no LOCK prefix: if the address computation
returns offset `off` through segment `seg` and leaves state `t`, RIP-relative handling gives `addr`,
whose linear address in `seg` is `lin` (`SegAccess`: `addr` for a flat segment, `base + addr` for FS
or GS), and the `n / 8` bytes at `lin` can be written in place (`MemWritable`), the form succeeds
and equals: read the `reg` register (extended by REX.R) in `t`, set `Next_IP := next`, and write its
value to those bytes (`dataAccess t "store"`: the write's bookkeeping).
-/
theorem mov_m_r_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : MemWritable t lin (n / 8)) :
    (X86.Instructions.MOV_MEMv_GPRv_1 ip ctx mod reg rm).run s =
      let src : Operand n := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand n) (movSpec (src.read t))
        next) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 64 (by decide)
      ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 64).read t) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_GPRv_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR64_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]
  · have hcontext :
        {ctx with operand_size := 32, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 32 (by decide)
      ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 32).read t) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_GPRv_1
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with (readGPR32_run _ _ hmode)
    refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]

/--
Layer 2 for `MOV_MEMv_GPRv_1` at operand size 16 (`66 89 /r`, `mod ≠ 3`): as `mov_m_r_form`, the low
16 bits of the `reg` register stored to the 2 bytes at `addr`. The generated
`Instructions/Mov/Generated/MR` uses it.
-/
theorem mov_m16_r16_form [Bindings] {asz : Int} (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (hsize : ctx.operand_size = 16)
    (haddr : ctx.address_size = asz) (hlock : ctx.lock_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s =
      (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address asz isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hw : MemWritable t lin 2) :
    (X86.Instructions.MOV_MEMv_GPRv_1 ip ctx mod reg rm).run s =
      let src : Operand 16 := .reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 16) (movSpec (src.read t))
        next) := by
  have hcontext :
      {ctx with operand_size := 16, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (ht.withNextIP next) seg addr lin hseg 16 (by decide)
    ((Operand.reg (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 16).read t) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMv_GPRv_1
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with (readGPR16_run _ _ hmode)
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]

/--
Layer 2 for `MOV_MEMv_IMMz_1` (`C7 /0 id`, `mod ≠ 3`) at operand size `n` (64 or 32). As
`mov_m_r_form` (any segment: the write is at `addr`'s linear address `lin`; any address size
`asz`), except that the
source is the 32-bit immediate fetched at `next` (the address after the displacement; state `t`
to `u`), sign-extended to `n` bits, and both `Next_IP` and the RIP-relative base are `next + 4`.
-/
theorem mov_m_imm32_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context)
    (mod : BitVec 2) (rm : BitVec 3) (n : Nat) (hn : n = 64 ∨ n = 32)
    (hsize : ctx.operand_size = n) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 32)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 32).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 4#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (hu : DataReady u) (hw : MemWritable u lin (n / 8)) :
    (X86.Instructions.MOV_MEMv_IMMz_1 ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess u "store") (.mem lin : Operand n)
        (movSpec (imm.signExtend n)) (BitVec.add next 4#64)) := by
  rcases hn with rfl | rfl
  · have hcontext :
        {ctx with operand_size := 64, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (hu.withNextIP (BitVec.add next 4#64)) seg addr lin
      hseg 64
      (by decide) (imm.signExtend 64) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_IMMz_1
    have hrip' : ∀ X, X = BitVec.add next 4#64 →
        Handle_RIP_Relative_Address asz isRip off X = .ok addr := fun X hX => hX ▸ hrip
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with hfetch
    iterate 3 spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]
  · have hcontext :
        {ctx with operand_size := 32, address_size := asz, lock_prefix_present := false} = ctx := by
      cases ctx
      simp_all
    rw [← hcontext]
    have hwrite := logicalMemWrite_run_seg _ (hu.withNextIP (BitVec.add next 4#64)) seg addr lin
      hseg 32
      (by decide) (imm.signExtend 32) hw.low hw.mem
    unfold X86.Instructions.MOV_MEMv_IMMz_1
    have hrip' : ∀ X, X = BitVec.add next 4#64 →
        Handle_RIP_Relative_Address asz isRip off X = .ok addr := fun X hX => hX ▸ hrip
    refine (specM_bind_run _ _ hea).trans ?_
    repeat spec_bind_rfl
    spec_bind_with hfetch
    iterate 3 spec_bind_rfl
    refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
    spec_run [Logical_Mem_Write => hwrite]

/--
Layer 2 for `MOV_MEMv_IMMz_1` at operand size 16 (`66 C7 /0 iw`): as `mov_m_imm32_form`, with a
16-bit immediate and `Next_IP` = `next + 2`.
-/
theorem mov_m_imm16_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (hsize : ctx.operand_size = 16) (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 16)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 16).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 2#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (hu : DataReady u) (hw : MemWritable u lin 2) :
    (X86.Instructions.MOV_MEMv_IMMz_1 ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess u "store") (.mem lin : Operand 16)
        (movSpec (imm.signExtend 16)) (BitVec.add next 2#64)) := by
  have hcontext :
      {ctx with operand_size := 16, address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (hu.withNextIP (BitVec.add next 2#64)) seg addr lin
    hseg 16
    (by decide) (imm.signExtend 16) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMv_IMMz_1
  have hrip' : ∀ X, X = BitVec.add next 2#64 →
      Handle_RIP_Relative_Address asz isRip off X = .ok addr := fun X hX => hX ▸ hrip
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with hfetch
  iterate 3 spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]

/--
Layer 2 for `MOV_MEMb_IMMb_1` (`C6 /0 ib`, `mod ≠ 3`): as `mov_m_imm32_form`, with an 8-bit
immediate written to one byte and `Next_IP` = `next + 1`.
-/
theorem mov_m8_imm8_form [Bindings] {asz : Int} (s t u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (rm : BitVec 3)
    (haddr : ctx.address_size = asz)
    (hlock : ctx.lock_prefix_present = false) (off next addr : BitVec 64) (seg : Segment)
    (isRip : Bool) {baseUsesRsp : Bool} (imm : BitVec 8)
    (hea : (Effective_Address asz ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hfetch : (Mem_Fetch next 8).run t = (.ok imm, u))
    (hrip : Handle_RIP_Relative_Address asz isRip off (BitVec.add next 1#64) = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (hu : DataReady u) (hw : MemWritable u lin 1) :
    (X86.Instructions.MOV_MEMb_IMMb_1 ip ctx mod rm).run s =
      (.ok (), writeResult (dataAccess u "store") (.mem lin : Operand 8)
        (movSpec (imm.signExtend 8)) (BitVec.add next 1#64)) := by
  have hcontext : {ctx with address_size := asz, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  have hwrite := logicalMemWrite_run_seg _ (hu.withNextIP (BitVec.add next 1#64)) seg addr lin
    hseg 8
    (by decide) (imm.signExtend 8) hw.low hw.mem
  unfold X86.Instructions.MOV_MEMb_IMMb_1
  have hrip' : ∀ X, X = BitVec.add next 1#64 →
      Handle_RIP_Relative_Address asz isRip off X = .ok addr := fun X hX => hX ▸ hrip
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with hfetch
  iterate 2 spec_bind_rfl
  refine (specM_bind_run _ _ (s := u) (value := addr) (by rw [hrip' _ ?_]; rfl; rfl)).trans ?_
  spec_run [Logical_Mem_Write => hwrite]

end X86Proofs
