import X86Proofs.Step.Escape
import X86Proofs.Step.Address
import X86Proofs.Instructions.NopMem.Form
import X86Proofs.Step.Decode.Legacy1Opcode1F

/-!
# Decoding `0F 1F /0` with a memory operand (`NOP_MEMv_0F1F`), after `66` / `2E` prefixes

The multi-byte NOPs compilers emit for padding: `0F 1F /0` with a memory ModRM, possibly after
operand-size (`66`) and CS (`2E`) prefixes (none, `66`, `66 2E`, `66 66 66 2E`,
`66 66 66 66 2E`).

- `NopPrefix`: `66` or `2E`. `NopContext`: what the decode context after such prefixes satisfies
  (`nopContext_scan`): no segment override (in 64-bit mode `2E` is not one), no REX bits, no LOCK,
  address size 64. So the address computation sees `AddrContext` for any shape without REX.B/X
  (`NopContext.addrContext`).
- With `mod ≠ 3` and `reg = 0`, opcode `0F 1F` selects form 2, `NOP_MEMv_0F1F`
  (`decodeLegacy1Opcode1F_run_of_nop_memory`, `Step/Decode/Legacy1Opcode1F.lean`).
- `decodeLegacy1_run_of_0F_1F_memory`: `pre 0F 1F modrm rest` from the state `step_scan_legacy1` hands to
  `Decode_Legacy_1`.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/-- A prefix byte of the multi-byte NOPs: `66` (operand size) or `2E` (CS). -/
def NopPrefix (p : UInt8) : Prop := p = 0x66 ∨ p = 0x2E

instance (p : UInt8) : Decidable (NopPrefix p) := inferInstanceAs (Decidable (_ ∨ _))

/-- The decode-context facts the memory NOP needs: no segment override, 64-bit mode, no REX or
REX2 bits, no LOCK, address size 64. -/
structure NopContext (ctx : Instruction_Context) : Prop where
  seg : ctx.seg_prefix_present = false
  mode64 : ctx.is_mode64 = true
  b4 : ctx.rex_b4 = 0
  x4 : ctx.rex_x4 = 0
  b3 : ctx.rex_b3 = 0
  x3 : ctx.rex_x3 = 0
  lock : ctx.lock_prefix_present = false
  addr : ctx.address_size = 64
  rex2 : ctx.rex2_prefix_present = false

theorem NopContext.update {segs : PrefixSegments} {ctx : Instruction_Context} (h : NopContext ctx)
    {p : UInt8} (hp : NopPrefix p) : NopContext (prefixUpdate segs ctx p) := by
  obtain ⟨h1, h2, h3, h4, -, -, h7, h8, h9⟩ := h
  rcases hp with rfl | rfl <;> constructor <;> simp_all [prefixUpdate, clearRex]

/-- After any run of `66` / `2E` prefixes the context is a `NopContext`. -/
theorem nopContext_scan (seg : Segment) (segs : PrefixSegments) (pre : List UInt8) (hpre : ∀ p ∈ pre, NopPrefix p) :
    NopContext (scanContext seg segs pre) := by
  have hasz : ∀ (ctx : Instruction_Context) (pre : List UInt8), (∀ p ∈ pre, NopPrefix p) →
      (pre.foldl (prefixUpdate segs) ctx).asz_prefix_present = ctx.asz_prefix_present := by
    intro ctx pre hpre
    induction pre generalizing ctx with
    | nil => rfl
    | cons p pre ih =>
      rw [List.foldl_cons, ih _ (fun q hq => hpre q (List.mem_cons_of_mem _ hq))]
      rcases hpre p List.mem_cons_self with rfl | rfl <;> rfl
  suffices ∀ ctx, NopContext ctx → NopContext (pre.foldl (prefixUpdate segs) ctx) by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9⟩ :=
      this (legacyContext seg) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h9⟩
    show scanAddressSize (pre.foldl (prefixUpdate segs) (legacyContext seg)) = 64
    unfold scanAddressSize
    rw [hasz _ pre hpre]
    rfl
  induction pre with
  | nil => exact fun _ h => h
  | cons p pre ih =>
    intro ctx h
    exact ih (fun q hq => hpre q (List.mem_cons_of_mem _ hq)) _
      (h.update (hpre p List.mem_cons_self))

/-- A `NopContext` gives the address computation what it reads, for a shape without REX.B/X. -/
theorem NopContext.addrContext {ctx : Instruction_Context} (h : NopContext ctx) (am : AddrMode)
    (hb : am.rexB = 0) (hx : am.rexX = 0) : AddrContext ctx am :=
  ⟨h.seg, h.mode64, h.b4, h.x4, h.b3.trans hb.symm, h.x3.trans hx.symm⟩

theorem nopPrefix_scanPrefix {pre : List UInt8} (h : ∀ p ∈ pre, NopPrefix p) :
    ∀ p ∈ pre, ScanPrefix p :=
  scanPrefix_of_66_2e h

/--
Decoding `pre 0F 1F modrm rest` (`pre` a run of `66` / `2E` prefixes, `mod ≠ 3`, `reg = 0`) at RIP
below 4 GiB, from the state `step_scan_legacy1` hands to `Decode_Legacy_1` (`pre.length + 2` fetches):
`Decode_Legacy_1` fetches `1F` again and the ModRM byte (two more fetches) and calls
`NOP_MEMv_0F1F` at RIP + `pre.length + 3` (the address of `rest`).
-/
theorem decodeLegacy1_run_of_0F_1F_memory [Bindings] (s : RamState) (h : ReadyToStep s) (pre : List UInt8)
    (hpre : ∀ p ∈ pre, NopPrefix p) (hlen : pre.length + 3 ≤ 15) (modrm : UInt8)
    (hmod : modrmMod modrm ≠ 3) (hreg : modrmReg modrm = 0) (rest : List UInt8)
    (hcode : BytesAt s s.RIP (pre ++ 0x0F :: 0x1F :: modrm :: rest))
    (hlow : s.RIP.toNat + (pre ++ 0x0F :: 0x1F :: modrm :: rest).length ≤ 2^32) :
    (Decode_Legacy_1 (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 1)))
        (scanContext s.DS (PrefixSegments.ofState s) pre)).run (afterFetches (beforeFetch s) (pre.length + 2)) =
      some ((X86.Instructions.NOP_MEMv_0F1F (BitVec.add s.RIP (BitVec.ofNat 64 (pre.length + 3)))
        (scanContext s.DS (PrefixSegments.ofState s) pre) (modrmMod modrm) (modrmRm modrm)).run
          (afterFetches (beforeFetch s) (pre.length + 4))) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP (pre ++ 0x0F :: 0x1F :: modrm :: rest) :=
    hcode
  have f2 := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 2) hf hc hlow (pre.length + 1)
    (by simp) (by omega)
  have f3 := memFetch_run_of_bytesAt (beforeFetch s) (pre.length + 3) hf hc hlow (pre.length + 2)
    (by simp) (by omega)
  simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem_cons_succ, List.getElem_cons_zero] at f2 f3
  rw [show (beforeFetch s).RIP = s.RIP from rfl] at f2 f3
  rw [show pre.length + 2 + 1 = pre.length + 3 by omega] at f2
  rw [show pre.length + 3 + 1 = pre.length + 4 by omega,
    show pre.length + 2 = pre.length + 1 + 1 by omega, ← add_ofNat_add] at f3
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) (pre.length + 4)) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy1_run_of_opcode1F _ _ _ _ (nopContext_scan _ _ pre hpre).rex2 (hmode _) f2,
    decodeLegacy1Opcode1F_run_of_nop_memory _ _ _ _ _ hmod hreg (hmode _) hfeatures f3, add_ofNat_add,
    show pre.length + 1 + 2 = pre.length + 3 by omega]
  rfl

end X86Proofs
