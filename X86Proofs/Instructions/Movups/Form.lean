import X86Proofs.Step.Sse
import X86Proofs.Step.Address
import X86Proofs.Program.ReadWrite.WriteResult
import X86Proofs.Instructions.Movups.Operation

/-!
# Layer 2: `MOVUPS_XMMps_MEMps` (`0F 10 /r`, memory operand)

`movups xmm, m128`: compute the address (`Effective_Address`, then
`Handle_RIP_Relative_Address`), pass the prefix checks (no LOCK, `66` or `F2`/`F3`) and the SSE
control-register checks (`Prelude.SupportedSSE`), read 16 bytes at the address through the flat
data segment with alignment type `Explicitly_Unaligned` (no alignment requirement; the read may
cross a page), set `Next_IP`, and write the value to the `reg` XMM register, keeping bits 128–511
of its ZMM register (a legacy SSE write). No flags.

lean-x86's `MOVUP` (four 32-bit lanes copied into a zero register) at 128 bits is the identity
(`movup_operation`, `Movups/Operation.lean`).

As for `mov_r_m_form`, the address computation is a hypothesis (`hea`, `hrip`), discharged for
an `AddrMode` by `effectiveAddress_run` and `handleRIPRelativeAddress_addrMode_run`.
`movups_xmm_m_seg_form` is the form through any segment (an FS/GS override: the read is at the
linear address `lin`, `SegAccess`); `movups_xmm_m_form`, the flat-segment case, is its corollary.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- The 5-bit register number the SSE forms compute from REX.R4, REX.R and the `reg` field. -/
theorem concatBits_xmm_reg (a b : BitVec 1) (c : BitVec 3) : (BitVec.ofNat (2 + 3 : Int).toNat
    ((BitVec.ofNat (1 + 1 : Int).toNat (a.toNat <<< Int.toNat 1 + b.toNat)).toNat <<<
      Int.toNat 3 + c.toNat) : BitVec 5) = gprNumber a b c := rfl

/--
Layer 2 for `MOVUPS_XMMps_MEMps` (`0F 10 /r`, `mod ≠ 3`) through any segment (an FS/GS override
or the flat data segment). In 64-bit mode, with address size 64, SSE enabled and no LOCK, `66`,
`F2`/`F3`, VEX or EVEX prefix: if the address computation returns offset `off` through segment
`seg` and leaves state `t`, RIP-relative handling gives `addr`, whose linear address in `seg` is
`lin` (`SegAccess`), and the 16 bytes at `lin` lie below 4 GiB and are present in RAM, the form
succeeds and equals: read them (`dataAccess t "load"`), set `Next_IP := next`, and write the
value to the `reg` XMM register.
-/
theorem movups_xmm_m_seg_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hrep : ctx.rep_prefix = 0)
    (hlock : ctx.lock_prefix_present = false) (hosz : ctx.osz_prefix_present = false)
    (hvex : ctx.vex_prefix_present = false) (hevex : ctx.evex_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hlow : lin.toNat + 16 ≤ 2^32)
    (hmem : ∀ i, i < 16 → (t.external[lin + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOVUPS_XMMps_MEMps ip ctx mod reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst ((Operand.mem lin : Operand 128).read t)
        next) := by
  have hread := logicalMemRead_run_seg_align t ht seg addr lin hseg 128 (by decide) .Memory_Read
    (.inl rfl) .Explicitly_Unaligned (AlignmentOk.unaligned _ _) hlow hmem
  unfold X86.Instructions.MOVUPS_XMMps_MEMps
  simp only [haddr, hrep, hlock, hosz, hvex, hevex, movup_operation]
  refine (specM_bind_run _ _ hea).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    Logical_Mem_Read => hread]
  have hm' : In64BitMode { dataAccess t "load" with Next_IP := next } := hmode.of_cs_lma_eq rfl rfl
  refine (writeXMM128_run _ _ _ hm').trans ?_
  simp only [writeResult, Operand.write_xmm, concatBits_xmm_reg]

/--
Layer 2 for `MOVUPS_XMMps_MEMps` (`0F 10 /r`, `mod ≠ 3`). In 64-bit mode, with address size 64,
SSE enabled and no LOCK, `66`, `F2`/`F3`, VEX or EVEX prefix: if the address computation returns
offset `off` through a flat data segment and leaves state `t`, RIP-relative handling gives
`addr`, and the 16 bytes at `addr` lie below 4 GiB and are present in RAM, the form succeeds and
equals: read them (`dataAccess t "load"`), set `Next_IP := next`, and write the value to the
`reg` XMM register.
-/
theorem movups_xmm_m_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (haddr : ctx.address_size = 64)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (hvex : ctx.vex_prefix_present = false)
    (hevex : ctx.evex_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s =
      (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hlow : addr.toNat + 16 ≤ 2^32)
    (hmem : ∀ i, i < 16 → (t.external[addr + BitVec.ofNat 64 i]?).isSome) :
    (X86.Instructions.MOVUPS_XMMps_MEMps ip ctx mod reg rm).run s =
      let dst : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "load") dst ((Operand.mem addr : Operand 128).read t)
        next) :=
  movups_xmm_m_seg_form s t ip ctx mod reg rm haddr hrep hlock hosz hvex hevex off next addr _
    isRip hea hrip addr (SegAccess.flat isStack addr) ht hmode hsse hlow hmem

end X86Proofs
