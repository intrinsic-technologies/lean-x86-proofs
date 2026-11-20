import X86Proofs.Instructions.Enter.Generated.Frame.Step
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def enterL0Effect (p : BitVec 64) (len : Nat) (size : BitVec 16) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 4 : Operand 64), pushAddr s - size.setWidth 64⟩,
    ⟨(Operand.reg 5 : Operand 64), pushAddr s⟩,
    ⟨(Operand.mem (pushAddr s) : Operand 64), (Operand.reg 5 : Operand 64).read s⟩]

@[simp] theorem enterL0Effect_components (p : BitVec 64) (len : Nat) (size : BitVec 16)
    (s : RamState) :
    (enterL0Effect p len size s).components =
      [.reg 4, .reg 5, .mem (pushAddr s) 8, .rip] := by
  simp [enterL0Effect, Effect.components]

structure EnterL0Pre (p : BitVec 64) (codeLen : Nat) (size : BitVec 16) (s : RamState) : Prop where
  push : PushPre p codeLen s
  check : (pushAddr s - size.setWidth 64).toNat + 8 ≤ 2^32

theorem enter_l0_effect_step [Bindings] (p : BitVec 64) (size : BitVec 16) :
    StepEffect (EnterL0Pre p 4 size) (codeRange p (0xC8 :: (immBytes 16 size ++ [0x00])))
      (enterL0Effect p 4 size) := by
  intro s h hcode hpre
  have hp := hpre.push.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, enter_l0_step s h [] (by simp) (by simp) rfl rfl rfl rfl size hcode.bytesAt hlow
      hpre.push.write hpre.check,
    ReadyToStep.afterStep_enter0 h _ _ _ hpre.push.write.low hpre.push.write.tables,
    ⟨afterStep_enter0_rip h _ _ _, ⟨Operand.read_afterStep_enter0_rsp _ _ _ _,
      Operand.read_afterStep_enter0_rbp _ _ _ _,
      Operand.read_afterStep_enter0_mem _ _ _ _⟩, trivial,
      (enterL0Effect_components s.RIP 4 size s).symm ▸ AgreesExcept.afterStep_enter0 _ _ _ _⟩⟩

theorem enter_l0_triple [Bindings] (p : BitVec 64) (size : BitVec 16) :
    Triple (EnterL0Pre p 4 size) (codeRange p (0xC8 :: (immBytes 16 size ++ [0x00])))
      (Effect.post (enterL0Effect p 4 size)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_components_enter0
    (enterL0Effect_components p 4 size s) (by simpa using hpre.push.code))
    (enter_l0_effect_step p size)

def enterL1Effect (p : BitVec 64) (len : Nat) (size : BitVec 16) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 4 : Operand 64), pushAddr s - 8 - size.setWidth 64⟩,
    ⟨(Operand.reg 5 : Operand 64), pushAddr s⟩,
    ⟨(Operand.mem (pushAddr s) : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
    ⟨(Operand.mem (pushAddr s - 8) : Operand 64), pushAddr s⟩]

@[simp] theorem enterL1Effect_components (p : BitVec 64) (len : Nat) (size : BitVec 16)
    (s : RamState) :
    (enterL1Effect p len size s).components =
      [.reg 4, .reg 5, .mem (pushAddr s) 8, .mem (pushAddr s - 8) 8, .rip] := by
  simp [enterL1Effect, Effect.components]

structure EnterL1Pre (p : BitVec 64) (codeLen : Nat) (size : BitVec 16) (s : RamState) : Prop where
  push : PushPre p codeLen s
  push2 : StorePre p codeLen (fun s => pushAddr s - 8) 8 s
  check : (pushAddr s - 8 - size.setWidth 64).toNat + 8 ≤ 2^32

theorem enter_l1_effect_step [Bindings] (p : BitVec 64) (size : BitVec 16) :
    StepEffect (EnterL1Pre p 4 size) (codeRange p (0xC8 :: (immBytes 16 size ++ [0x01])))
      (enterL1Effect p 4 size) := by
  intro s h hcode hpre
  have hp := hpre.push.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  exact ⟨_, enter_l1_step s h [] (by simp) (by simp) rfl rfl rfl rfl size hcode.bytesAt hlow
      hpre.push.write hpre.push2.write hpre.check,
    ReadyToStep.afterStep_enter1 h _ _ _ hpre.push.write.low hpre.push.write.tables
      hpre.push2.write.low hpre.push2.write.tables,
    ⟨afterStep_enter1_rip h _ _ _, ⟨Operand.read_afterStep_enter1_rsp _ _ _ _,
      Operand.read_afterStep_enter1_rbp _ _ _ _,
      Operand.read_afterStep_enter1_mem _ _ _ _,
      Operand.read_afterStep_enter1_mem2 _ _ _ _⟩, trivial,
      (enterL1Effect_components s.RIP 4 size s).symm ▸ AgreesExcept.afterStep_enter1 _ _ _ _⟩⟩

theorem enter_l1_triple [Bindings] (p : BitVec 64) (size : BitVec 16) :
    Triple (EnterL1Pre p 4 size) (codeRange p (0xC8 :: (immBytes 16 size ++ [0x01])))
      (Effect.post (enterL1Effect p 4 size)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_components_enter1
    (enterL1Effect_components p 4 size s) (by simpa using hpre.push.code)
    (by simpa using hpre.push2.code))
    (enter_l1_effect_step p size)

def enterLNEffect (p : BitVec 64) (len L : Nat) (size : BitVec 16) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 len
  writes := [⟨(Operand.reg 4 : Operand 64), pushAddr s - 8 * BitVec.ofNat 64 L - size.setWidth 64⟩,
    ⟨(Operand.reg 5 : Operand 64), pushAddr s⟩] ++ (List.range (L + 1)).map fun k =>
      ⟨(Operand.mem (pushAddr s - 8 * BitVec.ofNat 64 k) : Operand 64), enterSlotVal s L k⟩

@[simp] theorem enterLNEffect_components (p : BitVec 64) (len L : Nat) (size : BitVec 16)
    (s : RamState) :
    (enterLNEffect p len L size s).components =
      [.reg 4, .reg 5] ++ (List.range (L + 1)).map
        (fun k => Component.mem (pushAddr s - 8 * BitVec.ofNat 64 k) 8) ++ [.rip] := by
  simp [enterLNEffect, Effect.components, Function.comp_def]

structure EnterLNPre (p : BitVec 64) (codeLen L : Nat) (size : BitVec 16) (s : RamState) :
    Prop where
  rip : s.RIP = p
  write : ∀ k ≤ L, MemWritable s (pushAddr s - 8 * BitVec.ofNat 64 k) 8
  code : ∀ k ≤ L, RangeApart (pushAddr s - 8 * BitVec.ofNat 64 k) 8 p codeLen
  read : ∀ k, 0 < k → k < L →
    MemReadable s ((Operand.reg 5 : Operand 64).read s - 8 * BitVec.ofNat 64 k) 8
  apart : ∀ j, 0 < j → j < L → ∀ k ≤ L, RangeApart
    ((Operand.reg 5 : Operand 64).read s - 8 * BitVec.ofNat 64 j) 8
    (pushAddr s - 8 * BitVec.ofNat 64 k) 8
  check : (pushAddr s - 8 * BitVec.ofNat 64 L - size.setWidth 64).toNat + 8 ≤ 2^32

theorem enter_ln_effect_step [Bindings] (p : BitVec 64) (L : Nat) (hL : 2 ≤ L) (hL' : L < 32)
    (size : BitVec 16) :
    StepEffect (EnterLNPre p 4 L size) (codeRange p (0xC8 :: (immBytes 16 size ++ [UInt8.ofNat L])))
      (enterLNEffect p 4 L size) := by
  intro s h hcode hpre
  have hp := hpre.rip
  subst hp
  have hlow : s.RIP.toNat + 4 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simpa using this
  refine ⟨_, enter_ln_step s h [] (by simp) (by simp) rfl rfl rfl rfl size L hL hL'
      hcode.bytesAt hlow hpre.write (fun k hk => hpre.read (k + 1) (by omega) (by omega))
      hpre.check,
    ReadyToStep.afterStep_enterN h _ _ _ _ (by omega) hpre.write,
    ⟨afterStep_enterN_rip h _ _ _ _, ?_, trivial,
      (enterLNEffect_components s.RIP 4 L size s).symm ▸
        AgreesExcept.afterStep_enterN _ _ _ _ _ (by omega)⟩⟩
  rw [enterLNEffect, Write.allHold_iff]
  intro w hw
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hw
  rcases hw with (rfl | rfl) | ⟨k, hk, rfl⟩
  · exact Operand.read_afterStep_enterN_rsp _ _ _ _ _
  · exact Operand.read_afterStep_enterN_rbp _ _ _ _ _
  · exact Operand.read_afterStep_enterN_slot _ _ _ _ _ hL hL' k (by omega)
      (fun k hk => (hpre.write k hk).low) hpre.apart

theorem enter_ln_triple [Bindings] (p : BitVec 64) (L : Nat) (hL : 2 ≤ L) (hL' : L < 32)
    (size : BitVec 16) :
    Triple (EnterLNPre p 4 L size) (codeRange p (0xC8 :: (immBytes 16 size ++ [UInt8.ofNat L])))
      (Effect.post (enterLNEffect p 4 L size)) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_components_enterN
    (enterLNEffect_components p 4 L size s) (by simpa using hpre.code))
    (enter_ln_effect_step p L hL hL' size)

attribute [x86_compose] enterL0Effect enterL1Effect enterLNEffect enterSlotVal

@[x86_local] theorem enterL0Effect_local {p : BitVec 64} {len : Nat} {size : BitVec 16} :
    Effect.Local (enterL0Effect p len size) := by
  effect_local [enterL0Effect, pushAddr, stackPtr]

@[x86_local] theorem enterL1Effect_local {p : BitVec 64} {len : Nat} {size : BitVec 16} :
    Effect.Local (enterL1Effect p len size) := by
  effect_local [enterL1Effect, pushAddr, stackPtr]

@[x86_local] theorem enterLNEffect_local {p : BitVec 64} {len L : Nat} {size : BitVec 16} :
    Effect.Local (enterLNEffect p len L size) := by
  effect_local [enterLNEffect, enterSlotVal, pushAddr, stackPtr]

end X86Proofs
