import X86Proofs.Instructions.Cmps.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem repne_cmpsq_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 8) (hdst : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.REPNE_CMPSQ ip ctx).run t =
      (.ok (), repneCmpsSpec 64 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSQ
  exact compare_string_repeat_ne hcm t ip ctx h hmode 64 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst

theorem repne_cmpsq_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 8) (hdst : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.REPNE_CMPSQ ip ctx).run t =
      (.ok (), repneCmpsSegSpec (segBase ctx.segment) 64
        { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSQ
  exact compare_string_repeat_ne_seg hcm t ip ctx h hmode 64 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hcount hsrc hdst

theorem repne_cmpsq_down_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 8) (hdst : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.REPNE_CMPSQ ip ctx).run t =
      (.ok (), repneCmpsDownSpec 64 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSQ
  exact compare_string_repeat_ne_down hcm t ip ctx h hmode 64 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst

theorem repne_cmpsq_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_CMPSQ ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSQ
  exact compare_string_repeat_ne_zero t ip ctx 64 (by decide) hlock hm64 hasz hcount

theorem repne_cmpsd_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 4) (hdst : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.REPNE_CMPSD ip ctx).run t =
      (.ok (), repneCmpsSpec 32 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSD
  exact compare_string_repeat_ne hcm t ip ctx h hmode 32 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst

theorem repne_cmpsd_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 4) (hdst : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.REPNE_CMPSD ip ctx).run t =
      (.ok (), repneCmpsSegSpec (segBase ctx.segment) 32
        { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSD
  exact compare_string_repeat_ne_seg hcm t ip ctx h hmode 32 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hcount hsrc hdst

theorem repne_cmpsd_down_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 4) (hdst : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.REPNE_CMPSD ip ctx).run t =
      (.ok (), repneCmpsDownSpec 32 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSD
  exact compare_string_repeat_ne_down hcm t ip ctx h hmode 32 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst

theorem repne_cmpsd_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_CMPSD ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSD
  exact compare_string_repeat_ne_zero t ip ctx 32 (by decide) hlock hm64 hasz hcount

theorem repne_cmpsw_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 2) (hdst : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.REPNE_CMPSW ip ctx).run t =
      (.ok (), repneCmpsSpec 16 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSW
  exact compare_string_repeat_ne hcm t ip ctx h hmode 16 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst

theorem repne_cmpsw_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 2) (hdst : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.REPNE_CMPSW ip ctx).run t =
      (.ok (), repneCmpsSegSpec (segBase ctx.segment) 16
        { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSW
  exact compare_string_repeat_ne_seg hcm t ip ctx h hmode 16 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hcount hsrc hdst

theorem repne_cmpsw_down_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 2) (hdst : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.REPNE_CMPSW ip ctx).run t =
      (.ok (), repneCmpsDownSpec 16 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSW
  exact compare_string_repeat_ne_down hcm t ip ctx h hmode 16 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst

theorem repne_cmpsw_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_CMPSW ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSW
  exact compare_string_repeat_ne_zero t ip ctx 16 (by decide) hlock hm64 hasz hcount

theorem repne_cmpsb_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 1) (hdst : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.REPNE_CMPSB ip ctx).run t =
      (.ok (), repneCmpsSpec 8 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSB
  exact compare_string_repeat_ne hcm t ip ctx h hmode 8 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst

theorem repne_cmpsb_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 1) (hdst : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.REPNE_CMPSB ip ctx).run t =
      (.ok (), repneCmpsSegSpec (segBase ctx.segment) 8
        { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSB
  exact compare_string_repeat_ne_seg hcm t ip ctx h hmode 8 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hcount hsrc hdst

theorem repne_cmpsb_down_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagSet t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 1) (hdst : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.REPNE_CMPSB ip ctx).run t =
      (.ok (), repneCmpsDownSpec 8 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSB
  exact compare_string_repeat_ne_down hcm t ip ctx h hmode 8 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst

theorem repne_cmpsb_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_CMPSB ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSB
  exact compare_string_repeat_ne_zero t ip ctx 8 (by decide) hlock hm64 hasz hcount

theorem repne_cmpsq_a32_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 8) (hdst : MemReadable t (rdi.read t) 8)
    (hsl : (rsi.read t).toNat + 8 < 2^32) (hdl : (rdi.read t).toNat + 8 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REPNE_CMPSQ ip ctx).run t =
      (.ok (), repneCmpsSpec 64 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSQ
  exact compare_string_repeat_ne_a32 hcm t ip ctx h hmode 64 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst hsl hdl hcl

theorem repne_cmpsq_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_CMPSQ ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSQ
  exact compare_string_repeat_ne_zero_a32 t ip ctx 64 (by decide) hlock hm64 hasz hcount

theorem repne_cmpsd_a32_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 4) (hdst : MemReadable t (rdi.read t) 4)
    (hsl : (rsi.read t).toNat + 4 < 2^32) (hdl : (rdi.read t).toNat + 4 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REPNE_CMPSD ip ctx).run t =
      (.ok (), repneCmpsSpec 32 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSD
  exact compare_string_repeat_ne_a32 hcm t ip ctx h hmode 32 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst hsl hdl hcl

theorem repne_cmpsd_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_CMPSD ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSD
  exact compare_string_repeat_ne_zero_a32 t ip ctx 32 (by decide) hlock hm64 hasz hcount

theorem repne_cmpsw_a32_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 2) (hdst : MemReadable t (rdi.read t) 2)
    (hsl : (rsi.read t).toNat + 2 < 2^32) (hdl : (rdi.read t).toNat + 2 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REPNE_CMPSW ip ctx).run t =
      (.ok (), repneCmpsSpec 16 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSW
  exact compare_string_repeat_ne_a32 hcm t ip ctx h hmode 16 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst hsl hdl hcl

theorem repne_cmpsw_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_CMPSW ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSW
  exact compare_string_repeat_ne_zero_a32 t ip ctx 16 (by decide) hlock hm64 hasz hcount

theorem repne_cmpsb_a32_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hdf : DirectionFlagClear t.RFLAGS) (hcount : rcx.read t ≠ 0)
    (hsrc : MemReadable t (rsi.read t) 1) (hdst : MemReadable t (rdi.read t) 1)
    (hsl : (rsi.read t).toNat + 1 < 2^32) (hdl : (rdi.read t).toNat + 1 < 2^32) (hcl : (rcx.read t).toNat < 2^32) :
    (X86.Instructions.REPNE_CMPSB ip ctx).run t =
      (.ok (), repneCmpsSpec 8 { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSB
  exact compare_string_repeat_ne_a32 hcm t ip ctx h hmode 8 (by decide) hlock hseg hm64 hasz hds hes
    hdf hcount hsrc hdst hsl hdl hcl

theorem repne_cmpsb_a32_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hcount : rcx.read t = 0) :
    (X86.Instructions.REPNE_CMPSB ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  unfold X86.Instructions.REPNE_CMPSB
  exact compare_string_repeat_ne_zero_a32 t ip ctx 8 (by decide) hlock hm64 hasz hcount

end X86Proofs
