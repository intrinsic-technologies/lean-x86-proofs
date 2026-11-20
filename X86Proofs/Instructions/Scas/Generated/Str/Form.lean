
import X86Proofs.Instructions.Scas.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem scasq_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.SCASQ ip ctx).run t = (.ok (), scasSpec 64 { t with Next_IP := ip }) := by
  have hop := scan_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.SCASQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasd_form [Bindings]
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
    (hrd : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.SCASD_2 ip ctx).run t = (.ok (), scasSpec 32 { t with Next_IP := ip }) := by
  have hop := scan_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.SCASD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasw_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.SCASW_2 ip ctx).run t = (.ok (), scasSpec 16 { t with Next_IP := ip }) := by
  have hop := scan_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.SCASW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasb_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.SCASB ip ctx).run t = (.ok (), scasSpec 8 { t with Next_IP := ip }) := by
  have hop := scan_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.SCASB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasq_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.SCASQ ip ctx).run t = (.ok (), scasDownSpec 64 { t with Next_IP := ip }) := by
  have hop := scan_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.SCASQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasd_down_form [Bindings]
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
    (hrd : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.SCASD_2 ip ctx).run t = (.ok (), scasDownSpec 32 { t with Next_IP := ip }) := by
  have hop := scan_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.SCASD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasw_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.SCASW_2 ip ctx).run t = (.ok (), scasDownSpec 16 { t with Next_IP := ip }) := by
  have hop := scan_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.SCASW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasb_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.SCASB ip ctx).run t = (.ok (), scasDownSpec 8 { t with Next_IP := ip }) := by
  have hop := scan_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hes hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.SCASB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasq_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rdi.read t) 8)
    (hdl : (rdi.read t).toNat + 8 < 2^32) :
    (X86.Instructions.SCASQ ip ctx).run t = (.ok (), scasSpec 64 { t with Next_IP := ip }) := by
  have hop := scan_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 64 (by decide) ctx hes hdf (hrd.of_external_eq rfl) hdl
  unfold X86.Instructions.SCASQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasd_a32_form [Bindings]
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
    (hrd : MemReadable t (rdi.read t) 4)
    (hdl : (rdi.read t).toNat + 4 < 2^32) :
    (X86.Instructions.SCASD_2 ip ctx).run t = (.ok (), scasSpec 32 { t with Next_IP := ip }) := by
  have hop := scan_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 32 (by decide) ctx hes hdf (hrd.of_external_eq rfl) hdl
  unfold X86.Instructions.SCASD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasw_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rdi.read t) 2)
    (hdl : (rdi.read t).toNat + 2 < 2^32) :
    (X86.Instructions.SCASW_2 ip ctx).run t = (.ok (), scasSpec 16 { t with Next_IP := ip }) := by
  have hop := scan_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 16 (by decide) ctx hes hdf (hrd.of_external_eq rfl) hdl
  unfold X86.Instructions.SCASW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem scasb_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rdi.read t) 1)
    (hdl : (rdi.read t).toNat + 1 < 2^32) :
    (X86.Instructions.SCASB ip ctx).run t = (.ok (), scasSpec 8 { t with Next_IP := ip }) := by
  have hop := scan_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    (hmode.of_cs_lma_eq rfl rfl) 8 (by decide) ctx hes hdf (hrd.of_external_eq rfl) hdl
  unfold X86.Instructions.SCASB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

end X86Proofs
