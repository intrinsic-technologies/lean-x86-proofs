
import X86Proofs.Instructions.Cmps.Operation

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem cmpsq_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 8) (hdst : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.CMPSQ ip ctx).run t = (.ok (), cmpsSpec 64 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSQ
  exact compare_string_once hcm t ip ctx h hmode 64 (by decide) hlock hseg hm64 hasz hds hes hdf
    hrepf hsrc hdst

theorem cmpsq_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 8) (hdst : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.CMPSQ ip ctx).run t =
      (.ok (), cmpsSegSpec (segBase ctx.segment) 64 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSQ
  exact compare_string_once_seg hcm t ip ctx h hmode 64 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hrepf hsrc hdst

theorem cmpsd_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 4) (hdst : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.CMPSD ip ctx).run t = (.ok (), cmpsSpec 32 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSD
  exact compare_string_once hcm t ip ctx h hmode 32 (by decide) hlock hseg hm64 hasz hds hes hdf
    hrepf hsrc hdst

theorem cmpsd_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 4) (hdst : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.CMPSD ip ctx).run t =
      (.ok (), cmpsSegSpec (segBase ctx.segment) 32 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSD
  exact compare_string_once_seg hcm t ip ctx h hmode 32 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hrepf hsrc hdst

theorem cmpsw_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 2) (hdst : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.CMPSW ip ctx).run t = (.ok (), cmpsSpec 16 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSW
  exact compare_string_once hcm t ip ctx h hmode 16 (by decide) hlock hseg hm64 hasz hds hes hdf
    hrepf hsrc hdst

theorem cmpsw_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 2) (hdst : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.CMPSW ip ctx).run t =
      (.ok (), cmpsSegSpec (segBase ctx.segment) 16 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSW
  exact compare_string_once_seg hcm t ip ctx h hmode 16 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hrepf hsrc hdst

theorem cmpsb_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 1) (hdst : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.CMPSB ip ctx).run t = (.ok (), cmpsSpec 8 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSB
  exact compare_string_once hcm t ip ctx h hmode 8 (by decide) hlock hseg hm64 hasz hds hes hdf
    hrepf hsrc hdst

theorem cmpsb_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 1) (hdst : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.CMPSB ip ctx).run t =
      (.ok (), cmpsSegSpec (segBase ctx.segment) 8 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSB
  exact compare_string_once_seg hcm t ip ctx h hmode 8 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hrepf hsrc hdst

theorem cmpsq_down_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 8) (hdst : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.CMPSQ ip ctx).run t = (.ok (), cmpsDownSpec 64 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSQ
  exact compare_string_once_down hcm t ip ctx h hmode 64 (by decide) hlock hseg hm64 hasz hds hes hdf
    hrepf hsrc hdst

theorem cmpsq_down_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 8) (hdst : MemReadable t (rdi.read t) 8) :
    (X86.Instructions.CMPSQ ip ctx).run t =
      (.ok (), cmpsDownSegSpec (segBase ctx.segment) 64 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSQ
  exact compare_string_once_down_seg hcm t ip ctx h hmode 64 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hrepf hsrc hdst

theorem cmpsd_down_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 4) (hdst : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.CMPSD ip ctx).run t = (.ok (), cmpsDownSpec 32 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSD
  exact compare_string_once_down hcm t ip ctx h hmode 32 (by decide) hlock hseg hm64 hasz hds hes hdf
    hrepf hsrc hdst

theorem cmpsd_down_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 4) (hdst : MemReadable t (rdi.read t) 4) :
    (X86.Instructions.CMPSD ip ctx).run t =
      (.ok (), cmpsDownSegSpec (segBase ctx.segment) 32 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSD
  exact compare_string_once_down_seg hcm t ip ctx h hmode 32 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hrepf hsrc hdst

theorem cmpsw_down_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 2) (hdst : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.CMPSW ip ctx).run t = (.ok (), cmpsDownSpec 16 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSW
  exact compare_string_once_down hcm t ip ctx h hmode 16 (by decide) hlock hseg hm64 hasz hds hes hdf
    hrepf hsrc hdst

theorem cmpsw_down_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 2) (hdst : MemReadable t (rdi.read t) 2) :
    (X86.Instructions.CMPSW ip ctx).run t =
      (.ok (), cmpsDownSegSpec (segBase ctx.segment) 16 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSW
  exact compare_string_once_down_seg hcm t ip ctx h hmode 16 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hrepf hsrc hdst

theorem cmpsb_down_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 1) (hdst : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.CMPSB ip ctx).run t = (.ok (), cmpsDownSpec 8 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSB
  exact compare_string_once_down hcm t ip ctx h hmode 8 (by decide) hlock hseg hm64 hasz hds hes hdf
    hrepf hsrc hdst

theorem cmpsb_down_seg_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = true)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = false)
    (hsr : SegReady ctx.segment)
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagSet t.RFLAGS)
    (hsrc : MemReadable t (segBase ctx.segment + rsi.read t) 1) (hdst : MemReadable t (rdi.read t) 1) :
    (X86.Instructions.CMPSB ip ctx).run t =
      (.ok (), cmpsDownSegSpec (segBase ctx.segment) 8 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSB
  exact compare_string_once_down_seg hcm t ip ctx h hmode 8 (by decide) hlock hseg hsr hm64 hasz
    hes hdf hrepf hsrc hdst

theorem cmpsq_a32_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 8) (hdst : MemReadable t (rdi.read t) 8)
    (hsl : (rsi.read t).toNat + 8 < 2^32) (hdl : (rdi.read t).toNat + 8 < 2^32) :
    (X86.Instructions.CMPSQ ip ctx).run t = (.ok (), cmpsSpec 64 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSQ
  exact compare_string_once_a32 hcm t ip ctx h hmode 64 (by decide) hlock hseg hm64 hasz hds
    hes hdf hrepf hsrc hdst hsl hdl

theorem cmpsd_a32_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 4) (hdst : MemReadable t (rdi.read t) 4)
    (hsl : (rsi.read t).toNat + 4 < 2^32) (hdl : (rdi.read t).toNat + 4 < 2^32) :
    (X86.Instructions.CMPSD ip ctx).run t = (.ok (), cmpsSpec 32 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSD
  exact compare_string_once_a32 hcm t ip ctx h hmode 32 (by decide) hlock hseg hm64 hasz hds
    hes hdf hrepf hsrc hdst hsl hdl

theorem cmpsw_a32_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 2) (hdst : MemReadable t (rdi.read t) 2)
    (hsl : (rsi.read t).toNat + 2 < 2^32) (hdl : (rdi.read t).toNat + 2 < 2^32) :
    (X86.Instructions.CMPSW ip ctx).run t = (.ok (), cmpsSpec 16 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSW
  exact compare_string_once_a32 hcm t ip ctx h hmode 16 (by decide) hlock hseg hm64 hasz hds
    hes hdf hrepf hsrc hdst hsl hdl

theorem cmpsb_a32_form [inst : Bindings]
    (hcm : Prelude.Bindings.CompareMemory.SatisfiesSelectors (inst.compareMemory (σ := Ram)))
    (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context) (h : DataReady t)
    (hmode : In64BitMode t)
    (hlock : ctx.lock_prefix_present = false)
    (hseg : ctx.seg_prefix_present = false)
    (hm64 : ctx.is_mode64 = true)
    (hasz : ctx.asz_prefix_present = true)
    (hds : t.DS = {userStackSegment with is_stack := some false})
    (hes : t.ES = {userStackSegment with is_stack := some false})
    (hrepf : t.Repeat_String_Operation = false)
    (hdf : DirectionFlagClear t.RFLAGS)
    (hsrc : MemReadable t (rsi.read t) 1) (hdst : MemReadable t (rdi.read t) 1)
    (hsl : (rsi.read t).toNat + 1 < 2^32) (hdl : (rdi.read t).toNat + 1 < 2^32) :
    (X86.Instructions.CMPSB ip ctx).run t = (.ok (), cmpsSpec 8 { t with Next_IP := ip }) := by
  unfold X86.Instructions.CMPSB
  exact compare_string_once_a32 hcm t ip ctx h hmode 8 (by decide) hlock hseg hm64 hasz hds
    hes hdf hrepf hsrc hdst hsl hdl

end X86Proofs
