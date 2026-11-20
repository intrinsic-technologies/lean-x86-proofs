
import X86Proofs.Instructions.Stos.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem stosq_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 8) :
    (X86.Instructions.STOSQ ip ctx).run t = (.ok (), stosSpec 64 { t with Next_IP := ip }) := by
  have hop := store_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hes hdf (hwr.of_external_eq rfl)
  unfold X86.Instructions.STOSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosd_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 4) :
    (X86.Instructions.STOSD_2 ip ctx).run t = (.ok (), stosSpec 32 { t with Next_IP := ip }) := by
  have hop := store_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hes hdf (hwr.of_external_eq rfl)
  unfold X86.Instructions.STOSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosw_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 2) :
    (X86.Instructions.STOSW_2 ip ctx).run t = (.ok (), stosSpec 16 { t with Next_IP := ip }) := by
  have hop := store_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hes hdf (hwr.of_external_eq rfl)
  unfold X86.Instructions.STOSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosb_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 1) :
    (X86.Instructions.STOSB ip ctx).run t = (.ok (), stosSpec 8 { t with Next_IP := ip }) := by
  have hop := store_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hes hdf (hwr.of_external_eq rfl)
  unfold X86.Instructions.STOSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosq_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 8) :
    (X86.Instructions.STOSQ ip ctx).run t = (.ok (), stosDownSpec 64 { t with Next_IP := ip }) := by
  have hop := store_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hes hdf (hwr.of_external_eq rfl)
  unfold X86.Instructions.STOSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosd_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 4) :
    (X86.Instructions.STOSD_2 ip ctx).run t = (.ok (), stosDownSpec 32 { t with Next_IP := ip }) := by
  have hop := store_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hes hdf (hwr.of_external_eq rfl)
  unfold X86.Instructions.STOSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosw_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 2) :
    (X86.Instructions.STOSW_2 ip ctx).run t = (.ok (), stosDownSpec 16 { t with Next_IP := ip }) := by
  have hop := store_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hes hdf (hwr.of_external_eq rfl)
  unfold X86.Instructions.STOSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosb_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 1) :
    (X86.Instructions.STOSB ip ctx).run t = (.ok (), stosDownSpec 8 { t with Next_IP := ip }) := by
  have hop := store_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hes hdf (hwr.of_external_eq rfl)
  unfold X86.Instructions.STOSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosq_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 8)
    (hdl : (rdi.read t).toNat + 8 < 2^32) :
    (X86.Instructions.STOSQ ip ctx).run t = (.ok (), stosSpec 64 { t with Next_IP := ip }) := by
  have hop := store_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hes hdf (hwr.of_external_eq rfl) hdl
  unfold X86.Instructions.STOSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosd_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 4)
    (hdl : (rdi.read t).toNat + 4 < 2^32) :
    (X86.Instructions.STOSD_2 ip ctx).run t = (.ok (), stosSpec 32 { t with Next_IP := ip }) := by
  have hop := store_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hes hdf (hwr.of_external_eq rfl) hdl
  unfold X86.Instructions.STOSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosw_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 2)
    (hdl : (rdi.read t).toNat + 2 < 2^32) :
    (X86.Instructions.STOSW_2 ip ctx).run t = (.ok (), stosSpec 16 { t with Next_IP := ip }) := by
  have hop := store_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hes hdf (hwr.of_external_eq rfl) hdl
  unfold X86.Instructions.STOSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem stosb_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hwr : MemWritable t (rdi.read t) 1)
    (hdl : (rdi.read t).toNat + 1 < 2^32) :
    (X86.Instructions.STOSB ip ctx).run t = (.ok (), stosSpec 8 { t with Next_IP := ip }) := by
  have hop := store_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hes hdf (hwr.of_external_eq rfl) hdl
  unfold X86.Instructions.STOSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

end X86Proofs
