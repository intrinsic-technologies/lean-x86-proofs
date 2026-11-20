import X86Proofs.Program.ReadWrite.Enter

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem enter_l0_form [Bindings] (u v w : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (size : BitVec 16) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmodeu : In64BitMode u)
    (hssu : u.SS = userStackSegment) (hfetch : (Mem_Fetch ip 16).run u = (.ok size, v))
    (hlevel : (Mem_Fetch (BitVec.add ip 2#64) 8).run v = (.ok 0#8, w)) (h : DataReady w)
    (hss : w.SS = userStackSegment) (hw : MemWritable w (pushAddr w) 8)
    (hcheck : (pushAddr w - size.setWidth 64).toNat + 8 ≤ 2^32) :
    (X86.Instructions.ENTER_IMMw_IMMb ip ctx).run u =
      (.ok (), enterState0 { w with Next_IP := BitVec.add ip 3#64 } size) := by
  have henter := enter_operation0 { w with Next_IP := BitVec.add ip 3#64 }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) hss size (hw.of_external_eq rfl)
    hcheck
  have hsas : (Stack_Address_Size u.SS).run u = (.ok 64, u) := by
    rw [hssu]; exact stackAddressSize_run u hmodeu
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = r
  rcases hw1 r with rfl | rfl <;>
  · unfold X86.Instructions.ENTER_IMMw_IMMb
    spec_bind_with (get_run u)
    spec_bind_with hsas
    spec_bind_with hfetch
    spec_bind_rfl
    spec_bind_with hlevel
    spec_run [X86.Instructions.Operations.ENTER => henter]

theorem enter_l1_form [Bindings] (u v w : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (size : BitVec 16) (hmode64 : ctx.is_mode64 = true) (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmodeu : In64BitMode u)
    (hssu : u.SS = userStackSegment) (hfetch : (Mem_Fetch ip 16).run u = (.ok size, v))
    (hlevel : (Mem_Fetch (BitVec.add ip 2#64) 8).run v = (.ok 1#8, w)) (h : DataReady w)
    (hss : w.SS = userStackSegment) (hw : MemWritable w (pushAddr w) 8)
    (hw2 : MemWritable w (pushAddr w - 8) 8)
    (hcheck : (pushAddr w - 8 - size.setWidth 64).toNat + 8 ≤ 2^32) :
    (X86.Instructions.ENTER_IMMw_IMMb ip ctx).run u =
      (.ok (), enterState1 { w with Next_IP := BitVec.add ip 3#64 } size) := by
  have henter := enter_operation1 { w with Next_IP := BitVec.add ip 3#64 }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) hss size (hw.of_external_eq rfl) (hw2.of_external_eq rfl)
    hcheck
  have hsas : (Stack_Address_Size u.SS).run u = (.ok 64, u) := by
    rw [hssu]; exact stackAddressSize_run u hmodeu
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = r
  rcases hw1 r with rfl | rfl <;>
  · unfold X86.Instructions.ENTER_IMMw_IMMb
    spec_bind_with (get_run u)
    spec_bind_with hsas
    spec_bind_with hfetch
    spec_bind_rfl
    spec_bind_with hlevel
    spec_run [X86.Instructions.Operations.ENTER => henter]

theorem enter_ln_form [Bindings] (u v w : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (size : BitVec 16) (L : Nat) (hL : 2 ≤ L) (hL' : L < 32) (hmode64 : ctx.is_mode64 = true)
    (hosz : ctx.osz_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hmodeu : In64BitMode u)
    (hssu : u.SS = userStackSegment) (hfetch : (Mem_Fetch ip 16).run u = (.ok size, v))
    (hlevel : (Mem_Fetch (BitVec.add ip 2#64) 8).run v = (.ok (BitVec.ofNat 8 L), w))
    (h : DataReady w) (hss : w.SS = userStackSegment)
    (hw : ∀ k ≤ L, MemWritable w (pushAddr w - 8 * BitVec.ofNat 64 k) 8)
    (hr : ∀ k < L - 1,
      MemReadable w ((Operand.reg 5 : Operand 64).read w - 8 * BitVec.ofNat 64 (k + 1)) 8)
    (hcheck : (pushAddr w - 8 * BitVec.ofNat 64 L - size.setWidth 64).toNat + 8 ≤ 2^32) :
    (X86.Instructions.ENTER_IMMw_IMMb ip ctx).run u =
      (.ok (), enterStateN { w with Next_IP := BitVec.add ip 3#64 } L size) := by
  have henter := enter_operationN { w with Next_IP := BitVec.add ip 3#64 }
    (h.of_sameControls ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
      h.tables) hss size L hL hL' (fun k hk => (hw k hk).of_external_eq rfl)
    (fun k hk => (hr k hk).of_external_eq rfl) hcheck
  have hsas : (Stack_Address_Size u.SS).run u = (.ok 64, u) := by
    rw [hssu]; exact stackAddressSize_run u hmodeu
  have hw1 : ∀ w : BitVec 1, w = 0 ∨ w = 1 := by decide
  have hcontext : ({ ctx with
      is_mode64 := true, osz_prefix_present := false, lock_prefix_present := false,
      rex_w := ctx.rex_w } : Instruction_Context) = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  generalize ctx.rex_w = r
  rcases hw1 r with rfl | rfl <;>
  · unfold X86.Instructions.ENTER_IMMw_IMMb
    spec_bind_with (get_run u)
    spec_bind_with hsas
    spec_bind_with hfetch
    spec_bind_rfl
    spec_bind_with hlevel
    spec_run [X86.Instructions.Operations.ENTER => henter]

end X86Proofs
