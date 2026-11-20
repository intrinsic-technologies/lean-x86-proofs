
import X86Proofs.Instructions.Movs.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem movsq_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 8) (hwr : MemWritable t (rdi.read t) 8) :
    (X86.Instructions.MOVSQ ip ctx).run t = (.ok (), movsSpec 64 { t with Next_IP := ip }) := by
  have hop := mov_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsq_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 8) (hwr : MemWritable t (rdi.read t) 8) :
    (X86.Instructions.MOVSQ ip ctx).run t =
      (.ok (), movsSegSpec (segBase ctx.segment) 64 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsd_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 4) (hwr : MemWritable t (rdi.read t) 4) :
    (X86.Instructions.MOVSD_2 ip ctx).run t = (.ok (), movsSpec 32 { t with Next_IP := ip }) := by
  have hop := mov_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsd_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 4) (hwr : MemWritable t (rdi.read t) 4) :
    (X86.Instructions.MOVSD_2 ip ctx).run t =
      (.ok (), movsSegSpec (segBase ctx.segment) 32 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsw_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 2) (hwr : MemWritable t (rdi.read t) 2) :
    (X86.Instructions.MOVSW_2 ip ctx).run t = (.ok (), movsSpec 16 { t with Next_IP := ip }) := by
  have hop := mov_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsw_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 2) (hwr : MemWritable t (rdi.read t) 2) :
    (X86.Instructions.MOVSW_2 ip ctx).run t =
      (.ok (), movsSegSpec (segBase ctx.segment) 16 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsq_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 8) (hwr : MemWritable t (rdi.read t) 8) :
    (X86.Instructions.MOVSQ ip ctx).run t = (.ok (), movsDownSpec 64 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsq_down_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 8) (hwr : MemWritable t (rdi.read t) 8) :
    (X86.Instructions.MOVSQ ip ctx).run t =
      (.ok (), movsDownSegSpec (segBase ctx.segment) 64 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_down_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsd_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 4) (hwr : MemWritable t (rdi.read t) 4) :
    (X86.Instructions.MOVSD_2 ip ctx).run t = (.ok (), movsDownSpec 32 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsd_down_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 4) (hwr : MemWritable t (rdi.read t) 4) :
    (X86.Instructions.MOVSD_2 ip ctx).run t =
      (.ok (), movsDownSegSpec (segBase ctx.segment) 32 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_down_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsw_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 2) (hwr : MemWritable t (rdi.read t) 2) :
    (X86.Instructions.MOVSW_2 ip ctx).run t = (.ok (), movsDownSpec 16 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hseg hm64 hds hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsw_down_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 2) (hwr : MemWritable t (rdi.read t) 2) :
    (X86.Instructions.MOVSW_2 ip ctx).run t =
      (.ok (), movsDownSegSpec (segBase ctx.segment) 16 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_down_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hseg hsr hes hdf hrd.low hwr.low
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsq_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 8) (hwr : MemWritable t (rdi.read t) 8)
    (hsl : (rsi.read t).toNat + 8 < 2^32) (hdl : (rdi.read t).toNat + 8 < 2^32) :
    (X86.Instructions.MOVSQ ip ctx).run t = (.ok (), movsSpec 64 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hseg hm64 hds hes hdf hsl hdl
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsd_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 4) (hwr : MemWritable t (rdi.read t) 4)
    (hsl : (rsi.read t).toNat + 4 < 2^32) (hdl : (rdi.read t).toNat + 4 < 2^32) :
    (X86.Instructions.MOVSD_2 ip ctx).run t = (.ok (), movsSpec 32 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hseg hm64 hds hes hdf hsl hdl
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem movsw_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 2) (hwr : MemWritable t (rdi.read t) 2)
    (hsl : (rsi.read t).toNat + 2 < 2^32) (hdl : (rdi.read t).toNat + 2 < 2^32) :
    (X86.Instructions.MOVSW_2 ip ctx).run t = (.ok (), movsSpec 16 { t with Next_IP := ip }) := by
  have hop := mov_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hseg hm64 hds hes hdf hsl hdl
    hrd.mem hwr.mem
  unfold X86.Instructions.MOVSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

end X86Proofs
