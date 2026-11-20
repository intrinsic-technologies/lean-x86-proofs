import X86Proofs.Instructions.Shrd.Generated.MRCl.Step
import X86Proofs.Instructions.Shrd.Generated.MRCl.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def shrdM64R64ClEffect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (s : RamState) :
    Effect :=
  shrdM64R64Effect p len am src (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrdM64R64ClEffect_components (p : BitVec 64) (len : Nat)
    (am : AddrMode) (src : BitVec 5) (s : RamState) :
    (shrdM64R64ClEffect p len am src s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 8, .flags, .rip] := by
  simp [shrdM64R64ClEffect, shrdM64R64Effect, Effect.components]

def shrdM64R64ClSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (src : BitVec 5)
    (s : RamState) : Effect :=
  shrdM64R64SegEffect p len base am src (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrdM64R64ClSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (src : BitVec 5) (s : RamState) :
    (shrdM64R64ClSegEffect p len base am src s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 8, .flags, .rip] := by
  simp [shrdM64R64ClSegEffect, shrdM64R64SegEffect, Effect.components]

def shrdM64R64ClA32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (s : RamState) :
    Effect :=
  shrdM64R64A32Effect p len am src (shiftCount 64 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrdM64R64ClA32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (src : BitVec 5) (s : RamState) :
    (shrdM64R64ClA32Effect p len am src s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 8, .flags, .rip] := by
  simp [shrdM64R64ClA32Effect, shrdM64R64A32Effect, Effect.components]

def shrdM32R32ClEffect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (s : RamState) :
    Effect :=
  shrdM32R32Effect p len am src (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrdM32R32ClEffect_components (p : BitVec 64) (len : Nat)
    (am : AddrMode) (src : BitVec 5) (s : RamState) :
    (shrdM32R32ClEffect p len am src s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 4, .flags, .rip] := by
  simp [shrdM32R32ClEffect, shrdM32R32Effect, Effect.components]

def shrdM32R32ClSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (src : BitVec 5)
    (s : RamState) : Effect :=
  shrdM32R32SegEffect p len base am src (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrdM32R32ClSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (src : BitVec 5) (s : RamState) :
    (shrdM32R32ClSegEffect p len base am src s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 4, .flags, .rip] := by
  simp [shrdM32R32ClSegEffect, shrdM32R32SegEffect, Effect.components]

def shrdM32R32ClA32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (s : RamState) :
    Effect :=
  shrdM32R32A32Effect p len am src (shiftCount 32 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrdM32R32ClA32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (src : BitVec 5) (s : RamState) :
    (shrdM32R32ClA32Effect p len am src s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 4, .flags, .rip] := by
  simp [shrdM32R32ClA32Effect, shrdM32R32A32Effect, Effect.components]

def shrdM16R16ClEffect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (s : RamState) :
    Effect :=
  shrdM16R16Effect p len am src (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrdM16R16ClEffect_components (p : BitVec 64) (len : Nat)
    (am : AddrMode) (src : BitVec 5) (s : RamState) :
    (shrdM16R16ClEffect p len am src s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 2, .flags, .rip] := by
  simp [shrdM16R16ClEffect, shrdM16R16Effect, Effect.components]

def shrdM16R16ClSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (src : BitVec 5)
    (s : RamState) : Effect :=
  shrdM16R16SegEffect p len base am src (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrdM16R16ClSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (src : BitVec 5) (s : RamState) :
    (shrdM16R16ClSegEffect p len base am src s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 2, .flags, .rip] := by
  simp [shrdM16R16ClSegEffect, shrdM16R16SegEffect, Effect.components]

def shrdM16R16ClA32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (s : RamState) :
    Effect :=
  shrdM16R16A32Effect p len am src (shiftCount 16 ((Operand.reg 1 : Operand 8).read s)) s

@[simp] theorem shrdM16R16ClA32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (src : BitVec 5) (s : RamState) :
    (shrdM16R16ClA32Effect p len am src s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 2, .flags, .rip] := by
  simp [shrdM16R16ClA32Effect, shrdM16R16A32Effect, Effect.components]

theorem shrd_m64_r64_cl_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM64R64ClEffect p (4 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := shrd_m_r_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m64_r64_cl_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 8 (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM64R64ClEffect p (4 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM64R64ClEffect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shrd_m64_r64_cl_effect_step p rex hrex reg am hv hx hb)

theorem shrd_m32_r32_cl_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM32R32ClEffect p (3 + am.tail.length) am
        (gprNumber 0 0 reg)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := shrd_m_r_cl_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) []).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) []).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m32_r32_cl_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (RmwPre p am 4 (3 + am.tail.length))
      (codeRange p (0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM32R32ClEffect p (3 + am.tail.length) am
        (gprNumber 0 0 reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM32R32ClEffect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shrd_m32_r32_cl_effect_step p reg am hv hx hb)

theorem shrd_m32_r32_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM32R32ClEffect p (4 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := shrd_m_r_cl_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  have hsrc : gprNumber (rexContext s.DS rex.toBitVec).rex_r4
      (rexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m32_r32_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM32R32ClEffect p (4 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM32R32ClEffect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shrd_m32_r32_cl_rex_effect_step p rex hrex reg am hv hx hb)

theorem shrd_m16_r16_cl_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => RmwPre p am 2 (4 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (0x66 :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM16R16ClEffect p (4 + am.tail.length) am
        (gprNumber 0 0 reg)) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := shrd_m16_r16_cl_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg)
    hcode.bytesAt hlow (by exact hread)
  dsimp only at hstep
  have hsrc : gprNumber (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r4
      (scanContext s.DS (PrefixSegments.ofState s) [0x66]).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ hc _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m16_r16_cl_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => RmwPre p am 2 (4 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (0x66 :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM16R16ClEffect p (4 + am.tail.length) am
        (gprNumber 0 0 reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM16R16ClEffect_components]; exact mem_components_rmw _ _) hpre.1.code
    (by simp; omega))
    (shrd_m16_r16_cl_effect_step p reg am hv hx hb)

theorem shrd_m16_r16_cl_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => RmwPre p am 2 (5 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM16R16ClEffect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg)) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hstep := shrd_m16_r16_cl_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg)
    hcode.bytesAt hlow (by rw [scanContext_66_rex _ _ hr]; exact hread)
  simp only [scanContext_66_rex _ _ hr] at hstep
  have hsrc : gprNumber (oszRexContext s.DS rex.toBitVec).rex_r4
      (oszRexContext s.DS rex.toBitVec).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ hc _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m16_r16_cl_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => RmwPre p am 2 (5 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (0x66 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM16R16ClEffect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM16R16ClEffect_components]; exact mem_components_rmw _ _) hpre.1.code
    (by simp; omega))
    (shrd_m16_r16_cl_rex_effect_step p rex hrex reg am hv hx hb)

theorem shrd_m64_r64_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM64R64ClSegEffect p (5 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := shrd_m_r_cl_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m64_r64_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 8 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM64R64ClSegEffect p (5 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM64R64ClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code
    (by simp; omega))
    (shrd_m64_r64_cl_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem shrd_m32_r32_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM32R32ClSegEffect p (4 + am.tail.length) base am
        (gprNumber 0 0 reg)) := by
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := shrd_m_r_cl_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m32_r32_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (SegRmwPre p r base am 4 (4 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM32R32ClSegEffect p (4 + am.tail.length) base am
        (gprNumber 0 0 reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM32R32ClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code
    (by simp; omega))
    (shrd_m32_r32_cl_seg_effect_step p r base reg am hv hx hb)

theorem shrd_m32_r32_cl_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM32R32ClSegEffect p (5 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := shrd_m_r_cl_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m32_r32_cl_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM32R32ClSegEffect p (5 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM32R32ClSegEffect_components]; exact mem_components_rmw _ _) hpre.store.code
    (by simp; omega))
    (shrd_m32_r32_cl_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem shrd_m16_r16_cl_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => SegRmwPre p r base am 2 (5 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM16R16ClSegEffect p (5 + am.tail.length) base am
        (gprNumber 0 0 reg)) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := shrd_m16_r16_cl_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ hc _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m16_r16_cl_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => SegRmwPre p r base am 2 (5 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM16R16ClSegEffect p (5 + am.tail.length) base am
        (gprNumber 0 0 reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM16R16ClSegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code
    (by simp; omega))
    (shrd_m16_r16_cl_seg_effect_step p r base reg am hv hx hb)

theorem shrd_m16_r16_cl_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => SegRmwPre p r base am 2 (6 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM16R16ClSegEffect p (6 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg)) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := shrd_m16_r16_cl_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg)
    hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  have hsrc : gprNumber (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r4
      (withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s))).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ hc _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m16_r16_cl_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => SegRmwPre p r base am 2 (6 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM16R16ClSegEffect p (6 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM16R16ClSegEffect_components]; exact mem_components_rmw _ _) hpre.1.store.code
    (by simp; omega))
    (shrd_m16_r16_cl_rex_seg_effect_step p r base rex hrex reg am hv hx hb)

theorem shrd_m64_r64_cl_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM64R64ClA32Effect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := shrd_m_r_cl_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 64) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m64_r64_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 8 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM64R64ClA32Effect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM64R64ClA32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shrd_m64_r64_cl_a32_effect_step p rex hrex reg am hv hx hb)

theorem shrd_m32_r32_cl_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM32R32ClA32Effect p (4 + am.tail.length) am
        (gprNumber 0 0 reg)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := shrd_m_r_cl_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m32_r32_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (Rmw32Pre p am 4 (4 + am.tail.length))
      (codeRange p (0x67 :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM32R32ClA32Effect p (4 + am.tail.length) am
        (gprNumber 0 0 reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM32R32ClA32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shrd_m32_r32_cl_a32_effect_step p reg am hv hx hb)

theorem shrd_m32_r32_cl_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM32R32ClA32Effect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := shrd_m_r_cl_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (rexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (rexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 32) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m32_r32_cl_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM32R32ClA32Effect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM32R32ClA32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shrd_m32_r32_cl_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem shrd_m16_r16_cl_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    StepEffect (fun s => Rmw32Pre p am 2 (5 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM16R16ClA32Effect p (5 + am.tail.length) am
        (gprNumber 0 0 reg)) := by
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := shrd_m16_r16_cl_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r4
      (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])).rex_r3 reg =
      (gprNumber 0 0 reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ hc _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m16_r16_cl_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0) :
    Triple (fun s => Rmw32Pre p am 2 (5 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM16R16ClA32Effect p (5 + am.tail.length) am
        (gprNumber 0 0 reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM16R16ClA32Effect_components]; exact mem_components_rmw _ _) hpre.1.code
    (by simp; omega))
    (shrd_m16_r16_cl_a32_effect_step p reg am hv hx hb)

theorem shrd_m16_r16_cl_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    StepEffect (fun s => Rmw32Pre p am 2 (6 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (shrdM16R16ClA32Effect p (6 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg)) := by
  have hr := hrex.rexPrefix
  intro s h hcode ⟨hpre, hc⟩
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := shrd_m16_r16_cl_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz)
    hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  have hsrc : gprNumber (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r4
      (withAsz (oszRexContext s.DS rex.toBitVec)).rex_r3 reg =
      (gprNumber 0 (rexR rex.toBitVec) reg) := rfl
  rw [hsrc] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_rmw h _ _ _ _ _ hread.low htables,
    ⟨afterStep_rmw_rip h _ _ _ _ _, ?_, StatusFlagsOutcome.allows_store ?_ _,
      AgreesExcept.afterStep_rmw s _ _ _ _ _⟩⟩
  · exact (Operand.read_afterStep_rmw (n := 16) s _ (by decide) (by decide) _ _ _ _).trans
      (shrdSpec_fst _ _ _ _ hc _ _)
  · exact shrdFlags_allows _ _ _ _ _ _

theorem shrd_m16_r16_cl_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB) :
    Triple (fun s => Rmw32Pre p am 2 (6 + am.tail.length) s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xAD :: am.modrm reg :: am.tail))
      (Effect.post (shrdM16R16ClA32Effect p (6 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shrdM16R16ClA32Effect_components]; exact mem_components_rmw _ _) hpre.1.code
    (by simp; omega))
    (shrd_m16_r16_cl_rex_a32_effect_step p rex hrex reg am hv hx hb)

theorem shrd_m64_r64_cl_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (RmwPre p am 8 (encodeShrdM64R64Cl src am).length)
      (codeRange p (encodeShrdM64R64Cl src am))
      (Effect.post
        (shrdM64R64ClEffect p (encodeShrdM64R64Cl src am).length am
          (src.setWidth 5))) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := shrd_m64_r64_cl_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeShrdM64R64Cl
  rw [show (am.rexByte true src :: 0x0F :: 0xAD :: am.modrm (regLow src) :: am.tail).length =
    4 + am.tail.length by simp; omega]
  exact this

theorem shrd_m32_r32_cl_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (RmwPre p am 4 (encodeShrdM32R32Cl src am).length)
      (codeRange p (encodeShrdM32R32Cl src am))
      (Effect.post
        (shrdM32R32ClEffect p (encodeShrdM32R32Cl src am).length am
          (src.setWidth 5))) := by
  unfold encodeShrdM32R32Cl
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shrd_m32_r32_cl_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (0x0F :: 0xAD :: am.modrm (regLow src) :: am.tail).length =
      3 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shrd_m32_r32_cl_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (am.rexByte false src :: 0x0F :: 0xAD :: am.modrm (regLow src) ::
      am.tail).length = 4 + am.tail.length by simp; omega]
    exact this

theorem shrd_m16_r16_cl_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (fun s => RmwPre p am 2 (encodeShrdM16R16Cl src am).length s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (encodeShrdM16R16Cl src am))
      (Effect.post
        (shrdM16R16ClEffect p (encodeShrdM16R16Cl src am).length am
          (src.setWidth 5))) := by
  unfold encodeShrdM16R16Cl
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shrd_m16_r16_cl_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (0x66 :: 0x0F :: 0xAD :: am.modrm (regLow src) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shrd_m16_r16_cl_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (0x66 :: am.rexByte false src :: 0x0F :: 0xAD :: am.modrm (regLow src) ::
      am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem shrd_m64_r64_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 8 (r.prefixByte :: encodeShrdM64R64Cl src am).length)
      (codeRange p (r.prefixByte :: encodeShrdM64R64Cl src am))
      (Effect.post
        (shrdM64R64ClSegEffect p (r.prefixByte :: encodeShrdM64R64Cl src am).length base am
          (src.setWidth 5))) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := shrd_m64_r64_cl_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeShrdM64R64Cl
  rw [show (r.prefixByte :: am.rexByte true src :: 0x0F :: 0xAD :: am.modrm (regLow src) ::
    am.tail).length = 5 + am.tail.length by simp; omega]
  exact this

theorem shrd_m32_r32_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (SegRmwPre p r base am 4 (r.prefixByte :: encodeShrdM32R32Cl src am).length)
      (codeRange p (r.prefixByte :: encodeShrdM32R32Cl src am))
      (Effect.post
        (shrdM32R32ClSegEffect p (r.prefixByte :: encodeShrdM32R32Cl src am).length base am
          (src.setWidth 5))) := by
  unfold encodeShrdM32R32Cl
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shrd_m32_r32_cl_seg_triple_of_bytes p r base (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (r.prefixByte :: 0x0F :: 0xAD :: am.modrm (regLow src) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shrd_m32_r32_cl_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: am.rexByte false src :: 0x0F :: 0xAD :: am.modrm (regLow src) ::
      am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem shrd_m16_r16_cl_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) :
    Triple (fun s => SegRmwPre p r base am 2 (r.prefixByte :: encodeShrdM16R16Cl src am).length s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (r.prefixByte :: encodeShrdM16R16Cl src am))
      (Effect.post
        (shrdM16R16ClSegEffect p (r.prefixByte :: encodeShrdM16R16Cl src am).length base am
          (src.setWidth 5))) := by
  unfold encodeShrdM16R16Cl
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shrd_m16_r16_cl_seg_triple_of_bytes p r base (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (r.prefixByte :: 0x66 :: 0x0F :: 0xAD :: am.modrm (regLow src) :: am.tail).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shrd_m16_r16_cl_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: 0x66 :: am.rexByte false src :: 0x0F :: 0xAD :: am.modrm (regLow src) ::
      am.tail).length = 6 + am.tail.length by simp; omega]
    exact this

theorem shrd_m64_r64_cl_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (Rmw32Pre p am 8 (0x67 :: encodeShrdM64R64Cl src am).length)
      (codeRange p (0x67 :: encodeShrdM64R64Cl src am))
      (Effect.post
        (shrdM64R64ClA32Effect p (0x67 :: encodeShrdM64R64Cl src am).length am (src.setWidth 5))) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := shrd_m64_r64_cl_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
  rw [hr, gprNumber_reg] at this
  unfold encodeShrdM64R64Cl
  rw [show (0x67 :: am.rexByte true src :: 0x0F :: 0xAD :: am.modrm (regLow src) ::
    am.tail).length = 5 + am.tail.length by simp; omega]
  exact this

theorem shrd_m32_r32_cl_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (Rmw32Pre p am 4 (0x67 :: encodeShrdM32R32Cl src am).length)
      (codeRange p (0x67 :: encodeShrdM32R32Cl src am))
      (Effect.post
        (shrdM32R32ClA32Effect p (0x67 :: encodeShrdM32R32Cl src am).length am (src.setWidth 5))) := by
  unfold encodeShrdM32R32Cl
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shrd_m32_r32_cl_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (0x67 :: 0x0F :: 0xAD :: am.modrm (regLow src) :: am.tail).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shrd_m32_r32_cl_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: am.rexByte false src :: 0x0F :: 0xAD :: am.modrm (regLow src) ::
      am.tail).length = 5 + am.tail.length by simp; omega]
    exact this

theorem shrd_m16_r16_cl_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) :
    Triple (fun s => Rmw32Pre p am 2 (0x67 :: encodeShrdM16R16Cl src am).length s ∧
        shiftCount 16 ((Operand.reg 1 : Operand 8).read s) ≤ 16)
      (codeRange p (0x67 :: encodeShrdM16R16Cl src am))
      (Effect.post
        (shrdM16R16ClA32Effect p (0x67 :: encodeShrdM16R16Cl src am).length am (src.setWidth 5))) := by
  unfold encodeShrdM16R16Cl
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shrd_m16_r16_cl_a32_triple_of_bytes p (regLow src) am hv hx hb
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (0x67 :: 0x66 :: 0x0F :: 0xAD :: am.modrm (regLow src) :: am.tail).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shrd_m16_r16_cl_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: 0x66 :: am.rexByte false src :: 0x0F :: 0xAD :: am.modrm (regLow src) ::
      am.tail).length = 6 + am.tail.length by simp; omega]
    exact this

attribute [x86_compose] shrdM64R64ClEffect shrdM32R32ClEffect shrdM16R16ClEffect shrdM64R64ClSegEffect shrdM32R32ClSegEffect shrdM16R16ClSegEffect shrdM64R64ClA32Effect shrdM32R32ClA32Effect shrdM16R16ClA32Effect

@[x86_local] theorem shrdM64R64ClEffect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} :
    Effect.Local (shrdM64R64ClEffect p len am src) :=
  Effect.Local.of_param (e := fun c => shrdM64R64Effect p len am src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrdM64R64Effect_local

@[x86_local] theorem shrdM64R64ClSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {src : BitVec 5} :
    Effect.Local (shrdM64R64ClSegEffect p len base am src) :=
  Effect.Local.of_param (e := fun c => shrdM64R64SegEffect p len base am src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrdM64R64SegEffect_local

@[x86_local] theorem shrdM64R64ClA32Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} :
    Effect.Local (shrdM64R64ClA32Effect p len am src) :=
  Effect.Local.of_param (e := fun c => shrdM64R64A32Effect p len am src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrdM64R64A32Effect_local

@[x86_local] theorem shrdM32R32ClEffect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} :
    Effect.Local (shrdM32R32ClEffect p len am src) :=
  Effect.Local.of_param (e := fun c => shrdM32R32Effect p len am src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrdM32R32Effect_local

@[x86_local] theorem shrdM32R32ClSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {src : BitVec 5} :
    Effect.Local (shrdM32R32ClSegEffect p len base am src) :=
  Effect.Local.of_param (e := fun c => shrdM32R32SegEffect p len base am src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrdM32R32SegEffect_local

@[x86_local] theorem shrdM32R32ClA32Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} :
    Effect.Local (shrdM32R32ClA32Effect p len am src) :=
  Effect.Local.of_param (e := fun c => shrdM32R32A32Effect p len am src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrdM32R32A32Effect_local

@[x86_local] theorem shrdM16R16ClEffect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} :
    Effect.Local (shrdM16R16ClEffect p len am src) :=
  Effect.Local.of_param (e := fun c => shrdM16R16Effect p len am src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrdM16R16Effect_local

@[x86_local] theorem shrdM16R16ClSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {src : BitVec 5} :
    Effect.Local (shrdM16R16ClSegEffect p len base am src) :=
  Effect.Local.of_param (e := fun c => shrdM16R16SegEffect p len base am src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrdM16R16SegEffect_local

@[x86_local] theorem shrdM16R16ClA32Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} :
    Effect.Local (shrdM16R16ClA32Effect p len am src) :=
  Effect.Local.of_param (e := fun c => shrdM16R16A32Effect p len am src c)
    (fun _ _ h => congrArg _ (h.read_reg _)) fun _ => shrdM16R16A32Effect_local

end X86Proofs
