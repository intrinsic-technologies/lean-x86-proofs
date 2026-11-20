import X86Proofs.Step.Address
import X86Proofs.Step.FetchImm
import X86Proofs.Step.Sse
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Instructions.MovStore.Form
import X86Proofs.Instructions.Movaps.Operation

/-!
# Layer 2: `MOVAPS_MEMps_XMMps` (`0F 29 /r`, `mod ≠ 3`)

`movaps m128, xmm`: compute the address (`Effective_Address`, then
`Handle_RIP_Relative_Address`), read the source XMM register (`reg`), pass the prefix checks (no
`F2`/`F3`, LOCK or `66`) and the SSE control-register checks, set `Next_IP`, and write the 16
bytes through the flat data segment with alignment type `Explicitly_Aligned`
(`logicalMemWrite_run_align`: the address must be a multiple of 16, else #GP; a 16-aligned
16-byte write never crosses a page). No flags.

- `mova_run`: lean-x86's `MOVA` (MOVAPS's operation, a copy element by element) at 128 bits
  with 32-bit elements, lifted into the state monad, returns its source (`mova_operation`,
  `Movaps/Operation.lean`).
- `movaps_m_xmm_form`: the form, for any addressing shape (the address computation is a hypothesis,
  as for the integer stores in `MovStore/Form.lean`); `movaps_m_xmm_seg_form`: through any
  segment (an FS/GS override: the write at the linear address `lin`, `SegAccess`), of which
  `movaps_m_xmm_form` is the flat-segment case.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- `MOVA` lifted into the state monad: it returns its source and changes nothing. -/
theorem mova_run {σ : Type} (s : X86.State σ) (x : BitVec 128) :
    (liftM (X86.Instructions.Operations.MOVA 32 128 x) :
        X86.Runtime.SpecM X86.Exception (X86.State σ) (X86.Runtime.Bits 128)).run s =
      (.ok x, s) := by
  rw [mova_operation]
  rfl

/--
Layer 2 for `MOVAPS_MEMps_XMMps` (`0F 29 /r`, `mod ≠ 3`) through any segment (an FS/GS override or
the flat data segment). As `movaps_m_xmm_form`, with the address computation returning segment
`seg`, in which `addr`'s linear address is `lin` (`SegAccess`): `lin` a multiple of 16 and the 16
bytes at `lin` writable in place, the form writes the `reg` XMM register there.
-/
theorem movaps_m_xmm_seg_form [Bindings] (s t : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (mod : BitVec 2) (reg rm : BitVec 3)
    (haddr : ctx.address_size = 64) (hrep : ctx.rep_prefix = 0)
    (hlock : ctx.lock_prefix_present = false) (hosz : ctx.osz_prefix_present = false)
    (off next addr : BitVec 64) (seg : Segment) (isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, seg, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (lin : BitVec 64) (hseg : SegAccess seg addr lin)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (halign : lin.toNat % 16 = 0) (hw : MemWritable t lin 16) :
    (X86.Instructions.MOVAPS_MEMps_XMMps ip ctx mod reg rm).run s =
      let src : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem lin : Operand 128) (src.read t) next) := by
  have hwrite := logicalMemWrite_run_seg_align _ (ht.withNextIP next) seg addr lin hseg 128
    (by decide) ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read t)
    .Explicitly_Aligned (fun _ => halign) hw.low hw.mem
  have hread : ∀ r, r = gprNumber ctx.rex_r4 ctx.rex_r3 reg → (Read_XMM r 128).run t =
      (.ok ((Operand.xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg) : Operand 128).read t), t) := by
    rintro r rfl
    exact readXMM128_run _ _ hmode
  unfold X86.Instructions.MOVAPS_MEMps_XMMps
  simp only [haddr, hrep, hlock, hosz]
  refine (specM_bind_run _ _ hea).trans ?_
  repeat spec_bind_rfl
  spec_bind_with (hread _ (by rfl))
  refine (specM_bind_run _ _ (s := t) (value := addr) (by rw [hrip]; rfl)).trans ?_
  spec_run [
    X86.CR4.OSFXSR => cr4OSFXSR_run hsse,
    X86.CR0.EM => cr0EM_run hsse,
    X86.CR0.TS => cr0TS_run hsse,
    liftM => mova_run _ _]
  exact hwrite

/--
Layer 2 for `MOVAPS_MEMps_XMMps` (`0F 29 /r`, `mod ≠ 3`). In 64-bit mode, with SSE enabled,
address size 64 and no `F2`/`F3`, LOCK or `66` prefix: if the address computation returns offset
`off` through a flat data segment and leaves state `t`, RIP-relative handling gives `addr`, `addr`
is a multiple of 16, and the 16 bytes at `addr` can be written in place (`MemWritable`), the form
succeeds and equals: read the `reg` XMM register (extended by REX.R) in `t`, set
`Next_IP := next`, and write its value to those bytes (`dataAccess t "store"`: the write's
bookkeeping).
-/
theorem movaps_m_xmm_form [Bindings] (s t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (mod : BitVec 2) (reg rm : BitVec 3) (haddr : ctx.address_size = 64)
    (hrep : ctx.rep_prefix = 0) (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false) (off next addr : BitVec 64) (isStack isRip : Bool) {baseUsesRsp : Bool}
    (hea : (Effective_Address 64 ctx mod rm 1 ip).run s = (.ok (off, flatData isStack, next, isRip, baseUsesRsp), t))
    (hrip : Handle_RIP_Relative_Address 64 isRip off next = .ok addr)
    (ht : DataReady t) (hmode : In64BitMode t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (halign : addr.toNat % 16 = 0) (hw : MemWritable t addr 16) :
    (X86.Instructions.MOVAPS_MEMps_XMMps ip ctx mod reg rm).run s =
      let src : Operand 128 := .xmm (gprNumber ctx.rex_r4 ctx.rex_r3 reg)
      (.ok (), writeResult (dataAccess t "store") (.mem addr : Operand 128) (src.read t) next) :=
  movaps_m_xmm_seg_form s t ip ctx mod reg rm haddr hrep hlock hosz off next addr _ isRip hea hrip
    addr (SegAccess.flat isStack addr) ht hmode hsse halign hw

end X86Proofs
