import X86Proofs.Instructions.Movs.Operation

/-!
# Layer 2: `MOVSB`

lean-x86's `MOVSB` (opcode `A4` without a REP prefix: `movsb`): set `Next_IP`, then one
`MOV_STRING` of 8 bits. It does not touch `Repeat_String_Operation` (only the `REP_` forms do).
This file is the one place that unfolds `MOVSB` (architecture rule 5): besides `movsb_form` it has
the form lemmas the `string` family's MOVSB rows use (`movsb_seg_form`, `movsb_down_form`,
`movsb_down_seg_form`, `movsb_a32_form`; their Step and Triple files are generated).
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

/--
Layer 2 for `MOVSB` with 64-bit addresses: in 64-bit mode, with no REX2, LOCK, REP or segment
prefix, the direction flag clear and flat DS and ES, if the bytes at RSI and RDI lie below 4 GiB
and are present in RAM, the form succeeds and is `movsSpec 8` from the state with
`Next_IP := ip`.
-/
theorem movsb_form [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (h : DataReady t) (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : (rsi.read t).toNat + 1 ≤ 2^32) (hdst : (rdi.read t).toNat + 1 ≤ 2^32)
    (hsrcMem : (t.external[rsi.read t]?).isSome) (hdstMem : (t.external[rdi.read t]?).isSome) :
    (X86.Instructions.MOVSB ip ctx).run t = (.ok (), movsSpec 8 { t with Next_IP := ip }) := by
  have hmem (a : BitVec 64) (ha : (t.external[a]?).isSome) :
      ∀ i, i < 8 / 8 → (t.external[a + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    obtain rfl : i = 0 := by omega
    simpa using ha
  have hop := mov_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (.inl rfl) ctx hseg hm64 hds hes hdf hsrc hdst
    (hmem _ hsrcMem) (hmem _ hdstMem)
  unfold X86.Instructions.MOVSB
  simp only [haddr, hrex2, hlock, hrep, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

/-- Layer 2 for `MOVSB` behind an FS or GS prefix: as `movsb_form`, the source at
`segBase ctx.segment + RSI` (`movsSegSpec`). -/
theorem movsb_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 1)
    (hwr : MemWritable t (rdi.read t) 1) :
    (X86.Instructions.MOVSB ip ctx).run t =
      (.ok (), movsSegSpec (segBase ctx.segment) 8 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

/-- Layer 2 for `MOVSB` with the direction flag set: RSI and RDI step down by one
(`movsDownSpec`). -/
theorem movsb_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 1) (hwr : MemWritable t (rdi.read t) 1) :
    (X86.Instructions.MOVSB ip ctx).run t = (.ok (), movsDownSpec 8 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

/-- Layer 2 for `MOVSB` with the direction flag set, behind an FS or GS prefix
(`movsDownSegSpec`). -/
theorem movsb_down_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 1)
    (hwr : MemWritable t (rdi.read t) 1) :
    (X86.Instructions.MOVSB ip ctx).run t =
      (.ok (), movsDownSegSpec (segBase ctx.segment) 8 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_down_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

/-- Layer 2 for `MOVSB` at address size 32 (a `67` prefix: ESI, EDI): as `movsb_down_form` with
DF = 0, RSI and RDI below 4 GiB with the byte after each too (`mov_string_operation_a32`), so
the move is `movsSpec 8`. -/
theorem movsb_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 1) (hwr : MemWritable t (rdi.read t) 1)
    (hsl : (rsi.read t).toNat + 1 < 2^32) (hdl : (rdi.read t).toNat + 1 < 2^32) :
    (X86.Instructions.MOVSB ip ctx).run t = (.ok (), movsSpec 8 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hseg hm64 hds hes hdf hsl hdl
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

end X86Proofs
