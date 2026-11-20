import X86Proofs.Instructions.Movups.Form
import X86Proofs.Instructions.Xorps.Form

/-!
# Layer 2: `XORPS_XMMxud_MEMxud` (`0F 57 /r`, memory operand)

`xorps xmm, m128`: compute the address, read the destination (`reg`) XMM register, pass the
prefix checks (no `F2`/`F3`, LOCK or `66`) and the SSE control-register checks, read 16 bytes at
the address with alignment type `Explicitly_Aligned` (the address must be a multiple of 16, else
#GP), set `Next_IP`, and write the register xor the loaded value to the destination, keeping bits
128–511 of its ZMM register. No flags.

The proof steps through the start of the form by hand: `spec_run` times out on the bind on
`Handle_RIP_Relative_Address` (symbolic `isRip`) after `Read_XMM`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `XORPS_XMMxud_MEMxud` (`0F 57 /r`, `mod ≠ 3`) through any segment (an FS/GS override
or the flat data segment): as `movups_xmm_m_seg_form`, with the 16 bytes at the linear address
`lin` also aligned (`lin % 16 = 0`): the form succeeds and equals: read them
(`dataAccess t "load"`), set `Next_IP := next`, and write the `reg` XMM register (as in `t`) xor
the loaded value to that register.
-/
theorem xorps_xmm_m_seg_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hrep : ctx.rep_prefix = 0)
    (hlock : ctx.lock_prefix_present = false) (hosz : ctx.osz_prefix_present = false)
    (hvex : ctx.vex_prefix_present = false) (hevex : ctx.evex_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (halign : lin.toNat % 16 = 0) (hlow : lin.toNat + 16 ≤ 2^32)
    (hmem : ∀ i, i < 16 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.XORPS_XMMxud_MEMxud ip ctx mod reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst
        (dst.read t ^^^ (Operand.mem lin : Operand 128).read t) next) := by
  have hread := logicalMemRead_run_seg_align t ht seg addr lin hseg 128 (by decide) .Memory_Read
    (.inl rfl) .Explicitly_Aligned (fun _ => halign) hlow hmem
  unfold X86.Instructions.XORPS_XMMxud_MEMxud
  simp only [haddr, hrep, hlock, hosz, hvex, hevex]
  refine (specM_bind_run _ _ hea).trans ?_
  spec_bind_rfl
  spec_bind_rfl
  refine (specM_bind_run _ _ (readXMM128_run _ _ hmode)).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    Logical_Mem_Read => hread,
    X86.Instructions.Operations.PXOR => pxor_operation _ _]
  have hm' : In64BitMode { dataAccess t "load" with Next_IP := next } := hmode.of_cs_lma_eq rfl rfl
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, Operand.read_xmm, concatBits_xmm_reg]

/--
Layer 2 for `XORPS_XMMxud_MEMxud` (`0F 57 /r`, `mod ≠ 3`). As `movups_xmm_m_form`, with the 16 bytes
at `addr` also aligned (`addr % 16 = 0`): the form succeeds and equals: read them
(`dataAccess t "load"`), set `Next_IP := next`, and write the `reg` XMM register (as in `t`) xor
the loaded value to that register.
-/
theorem xorps_xmm_m_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (haddr : ctx.address_size = 64)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (halign : addr.toNat % 16 = 0) (hlow : addr.toNat + 16 ≤ 2^32)
    (hmem : ∀ i, i < 16 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.XORPS_XMMxud_MEMxud ip ctx mod reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst
        (dst.read t ^^^ (Operand.mem addr : Operand 128).read t) next) :=
  xorps_xmm_m_seg_form s t ip ctx mod reg rm haddr hrep hlock hosz hvex hevex off next addr _
    isRip hea hrip addr (SegAccess.flat isStack addr) ht hmode hsse halign hlow hmem

end X86Proofs
