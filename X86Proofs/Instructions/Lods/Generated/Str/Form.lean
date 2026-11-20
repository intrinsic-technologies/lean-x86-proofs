
import X86Proofs.Instructions.Lods.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem lodsq_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 8) :
    (X86.Instructions.LODSQ ip ctx).run t = (.ok (), lodsSpec 64 { t with Next_IP := ip }) := by
  have hop := load_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    64 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsq_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 8) :
    (X86.Instructions.LODSQ ip ctx).run t =
      (.ok (), lodsSegSpec (segBase ctx.segment) 64 { t with Next_IP := ip }) := by
  have hop := load_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    64 (by decide) ctx hseg hsr hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsd_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 4) :
    (X86.Instructions.LODSD_2 ip ctx).run t = (.ok (), lodsSpec 32 { t with Next_IP := ip }) := by
  have hop := load_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    32 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsd_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 4) :
    (X86.Instructions.LODSD_2 ip ctx).run t =
      (.ok (), lodsSegSpec (segBase ctx.segment) 32 { t with Next_IP := ip }) := by
  have hop := load_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    32 (by decide) ctx hseg hsr hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsw_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 2) :
    (X86.Instructions.LODSW_2 ip ctx).run t = (.ok (), lodsSpec 16 { t with Next_IP := ip }) := by
  have hop := load_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    16 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsw_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 2) :
    (X86.Instructions.LODSW_2 ip ctx).run t =
      (.ok (), lodsSegSpec (segBase ctx.segment) 16 { t with Next_IP := ip }) := by
  have hop := load_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    16 (by decide) ctx hseg hsr hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsb_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 1) :
    (X86.Instructions.LODSB ip ctx).run t = (.ok (), lodsSpec 8 { t with Next_IP := ip }) := by
  have hop := load_string_operation { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    8 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsb_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 1) :
    (X86.Instructions.LODSB ip ctx).run t =
      (.ok (), lodsSegSpec (segBase ctx.segment) 8 { t with Next_IP := ip }) := by
  have hop := load_string_operation_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    8 (by decide) ctx hseg hsr hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsq_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 8) :
    (X86.Instructions.LODSQ ip ctx).run t = (.ok (), lodsDownSpec 64 { t with Next_IP := ip }) := by
  have hop := load_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    64 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsq_down_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 8) :
    (X86.Instructions.LODSQ ip ctx).run t =
      (.ok (), lodsDownSegSpec (segBase ctx.segment) 64 { t with Next_IP := ip }) := by
  have hop := load_string_operation_down_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    64 (by decide) ctx hseg hsr hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsd_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 4) :
    (X86.Instructions.LODSD_2 ip ctx).run t = (.ok (), lodsDownSpec 32 { t with Next_IP := ip }) := by
  have hop := load_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    32 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsd_down_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 4) :
    (X86.Instructions.LODSD_2 ip ctx).run t =
      (.ok (), lodsDownSegSpec (segBase ctx.segment) 32 { t with Next_IP := ip }) := by
  have hop := load_string_operation_down_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    32 (by decide) ctx hseg hsr hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsw_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 2) :
    (X86.Instructions.LODSW_2 ip ctx).run t = (.ok (), lodsDownSpec 16 { t with Next_IP := ip }) := by
  have hop := load_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    16 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsw_down_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 2) :
    (X86.Instructions.LODSW_2 ip ctx).run t =
      (.ok (), lodsDownSegSpec (segBase ctx.segment) 16 { t with Next_IP := ip }) := by
  have hop := load_string_operation_down_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    16 (by decide) ctx hseg hsr hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsb_down_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 1) :
    (X86.Instructions.LODSB ip ctx).run t = (.ok (), lodsDownSpec 8 { t with Next_IP := ip }) := by
  have hop := load_string_operation_down { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    8 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsb_down_seg_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 64)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = true)
    (hsr : SegReady ctx.segment)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hrd : MemReadable t (segBase ctx.segment + rsi.read t) 1) :
    (X86.Instructions.LODSB ip ctx).run t =
      (.ok (), lodsDownSegSpec (segBase ctx.segment) 8 { t with Next_IP := ip }) := by
  have hop := load_string_operation_down_seg { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    8 (by decide) ctx hseg hsr hdf (hrd.of_external_eq rfl)
  unfold X86.Instructions.LODSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsq_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 1)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 8)
    (hsl : (rsi.read t).toNat + 8 < 2^32) :
    (X86.Instructions.LODSQ ip ctx).run t = (.ok (), lodsSpec 64 { t with Next_IP := ip }) := by
  have hop := load_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    64 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl) hsl
  unfold X86.Instructions.LODSQ
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsd_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hosz : ctx.osz_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 4)
    (hsl : (rsi.read t).toNat + 4 < 2^32) :
    (X86.Instructions.LODSD_2 ip ctx).run t = (.ok (), lodsSpec 32 { t with Next_IP := ip }) := by
  have hop := load_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    32 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl) hsl
  unfold X86.Instructions.LODSD_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hosz, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsw_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hw : ctx.rex_w = 0)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 2)
    (hsl : (rsi.read t).toNat + 2 < 2^32) :
    (X86.Instructions.LODSW_2 ip ctx).run t = (.ok (), lodsSpec 16 { t with Next_IP := ip }) := by
  have hop := load_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    16 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl) hsl
  unfold X86.Instructions.LODSW_2
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hw, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

theorem lodsb_a32_form [Bindings]
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (haddr : ctx.address_size = 32)
    (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false)
    (hrep : ctx.rep_prefix = 0)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS)
    (hrd : MemReadable t (rsi.read t) 1)
    (hsl : (rsi.read t).toNat + 1 < 2^32) :
    (X86.Instructions.LODSB ip ctx).run t = (.ok (), lodsSpec 8 { t with Next_IP := ip }) := by
  have hop := load_string_operation_a32 { t with Next_IP := ip } (h.of_sameControls
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl h.tables)
    8 (by decide) ctx hseg hm64 hds hdf (hrd.of_external_eq rfl) hsl
  unfold X86.Instructions.LODSB
  simp (config := { decide := true }) only [haddr, hrex2, hlock, hrep, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  exact hop

end X86Proofs
