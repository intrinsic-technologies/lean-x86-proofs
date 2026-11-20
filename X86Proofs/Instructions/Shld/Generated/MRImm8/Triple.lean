import X86Proofs.Instructions.Shld.Generated.MRImm8.Step
import X86Proofs.Instructions.Shld.Generated.MRImm8.Encode
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def shldM64R64Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 64), shldResult c a b⟩]
    flags := some (shldFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shldM64R64Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5)
    (c : Nat) (s : RamState) :
    (shldM64R64Effect p len am src c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 8, .flags, .rip] := by
  simp [shldM64R64Effect, Effect.components]

def shldM64R64SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (src : BitVec 5)
    (c : Nat) (s : RamState) : Effect :=
  let addr := base + am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 64), shldResult c a b⟩]
    flags := some (shldFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shldM64R64SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (src : BitVec 5) (c : Nat) (s : RamState) :
    (shldM64R64SegEffect p len base am src c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 8, .flags, .rip] := by
  simp [shldM64R64SegEffect, Effect.components]

def shldM64R64A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat)
    (s : RamState) : Effect :=
  let addr := am.addr32 s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 64).read s
  let b := (Operand.reg src : Operand 64).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 64), shldResult c a b⟩]
    flags := some (shldFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shldM64R64A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (src : BitVec 5) (c : Nat) (s : RamState) :
    (shldM64R64A32Effect p len am src c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 8, .flags, .rip] := by
  simp [shldM64R64A32Effect, Effect.components]

def shldM32R32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 32), shldResult c a b⟩]
    flags := some (shldFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shldM32R32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5)
    (c : Nat) (s : RamState) :
    (shldM32R32Effect p len am src c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 4, .flags, .rip] := by
  simp [shldM32R32Effect, Effect.components]

def shldM32R32SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (src : BitVec 5)
    (c : Nat) (s : RamState) : Effect :=
  let addr := base + am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 32), shldResult c a b⟩]
    flags := some (shldFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shldM32R32SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (src : BitVec 5) (c : Nat) (s : RamState) :
    (shldM32R32SegEffect p len base am src c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 4, .flags, .rip] := by
  simp [shldM32R32SegEffect, Effect.components]

def shldM32R32A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat)
    (s : RamState) : Effect :=
  let addr := am.addr32 s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 32).read s
  let b := (Operand.reg src : Operand 32).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 32), shldResult c a b⟩]
    flags := some (shldFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shldM32R32A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (src : BitVec 5) (c : Nat) (s : RamState) :
    (shldM32R32A32Effect p len am src c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 4, .flags, .rip] := by
  simp [shldM32R32A32Effect, Effect.components]

def shldM16R16Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat)
    (s : RamState) : Effect :=
  let addr := am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 16), shldResult c a b⟩]
    flags := some (shldFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shldM16R16Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5)
    (c : Nat) (s : RamState) :
    (shldM16R16Effect p len am src c s).components =
      [.mem (am.addr s (p + BitVec.ofNat 64 len)) 2, .flags, .rip] := by
  simp [shldM16R16Effect, Effect.components]

def shldM16R16SegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode) (src : BitVec 5)
    (c : Nat) (s : RamState) : Effect :=
  let addr := base + am.addr s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 16), shldResult c a b⟩]
    flags := some (shldFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shldM16R16SegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64)
    (am : AddrMode) (src : BitVec 5) (c : Nat) (s : RamState) :
    (shldM16R16SegEffect p len base am src c s).components =
      [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) 2, .flags, .rip] := by
  simp [shldM16R16SegEffect, Effect.components]

def shldM16R16A32Effect (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat)
    (s : RamState) : Effect :=
  let addr := am.addr32 s (p + BitVec.ofNat 64 len)
  let a := (Operand.mem addr : Operand 16).read s
  let b := (Operand.reg src : Operand 16).read s
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.mem addr : Operand 16), shldResult c a b⟩]
    flags := some (shldFlags (StatusFlags.ofRFLAGS s.RFLAGS) c a b) }

@[simp] theorem shldM16R16A32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (src : BitVec 5) (c : Nat) (s : RamState) :
    (shldM16R16A32Effect p len am src c s).components =
      [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) 2, .flags, .rip] := by
  simp [shldM16R16A32Effect, Effect.components]

theorem shld_m64_r64_imm8_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect (RmwPre p am 8 (5 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM64R64Effect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 64 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := shld_m_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 64 (.inl rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
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
      (shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m64_r64_imm8_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple (RmwPre p am 8 (5 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM64R64Effect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 64 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM64R64Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m64_r64_imm8_effect_step p rex hrex reg am hv hx hb imm)

theorem shld_m32_r32_imm8_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    StepEffect (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM32R32Effect p (4 + am.tail.length) am
        (gprNumber 0 0 reg) (shiftCount 32 imm)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := shld_m_r_imm8_step s h [] (by simp) (by simp) 32 (.inr rfl)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.legacy _ am hx hb).toSeg) imm
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
      (shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m32_r32_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    Triple (RmwPre p am 4 (4 + am.tail.length))
      (codeRange p (0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM32R32Effect p (4 + am.tail.length) am
        (gprNumber 0 0 reg) (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM32R32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m32_r32_imm8_effect_step p reg am hv hx hb imm)

theorem shld_m32_r32_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect (RmwPre p am 4 (5 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM32R32Effect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 32 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := shld_m_r_imm8_step s h [rex] (by simpa using hr.scanPrefix) (by simp) 32 (.inr rfl)
    (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg) imm
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
      (shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m32_r32_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple (RmwPre p am 4 (5 + am.tail.length))
      (codeRange p (rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM32R32Effect p (5 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM32R32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m32_r32_imm8_rex_effect_step p rex hrex reg am hv hx hb imm)

theorem shld_m16_r16_imm8_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    StepEffect (RmwPre p am 2 (5 + am.tail.length))
      (codeRange p (0x66 :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM16R16Effect p (5 + am.tail.length) am
        (gprNumber 0 0 reg) (shiftCount 16 imm)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := shld_m16_r16_imm8_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    (by exact rfl)
    (by rfl) (by rfl)
    (by rfl) reg am hv
    (by exact (AddrContext.osz _ am hx hb).toSeg) imm
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
      (shldSpec_fst _ _ _ _ hc _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m16_r16_imm8_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (RmwPre p am 2 (5 + am.tail.length))
      (codeRange p (0x66 :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM16R16Effect p (5 + am.tail.length) am
        (gprNumber 0 0 reg) (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM16R16Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m16_r16_imm8_effect_step p reg am hv hx hb imm hc)

theorem shld_m16_r16_imm8_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    StepEffect (RmwPre p am 2 (6 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM16R16Effect p (6 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 16 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hstep := shld_m16_r16_imm8_step s h [0x66, rex] (by simp [scanPrefix_66, hr.scanPrefix]) (by simp)
    (by rw [scanContext_66_rex _ _ hr]; exact hrex.operand_size_osz s.DS)
    (by rw [scanContext_66_rex _ _ hr]; rfl) (by rw [scanContext_66_rex _ _ hr]; rfl)
    (by rw [scanContext_66_rex _ _ hr]; rfl) reg am hv
    (by rw [scanContext_66_rex _ _ hr]; exact (AddrContext.oszRex _ _ am hx hb).toSeg) imm
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
      (shldSpec_fst _ _ _ _ hc _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m16_r16_imm8_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (RmwPre p am 2 (6 + am.tail.length))
      (codeRange p (0x66 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM16R16Effect p (6 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM16R16Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m16_r16_imm8_rex_effect_step p rex hrex reg am hv hx hb imm hc)

theorem shld_m64_r64_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 8 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM64R64SegEffect p (6 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 64 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := shld_m_r_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
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
      (shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m64_r64_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 8 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM64R64SegEffect p (6 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 64 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM64R64SegEffect_components]; exact mem_components_rmw _ _) hpre.store.code
    (by simp; omega))
    (shld_m64_r64_imm8_seg_effect_step p r base rex hrex reg am hv hx hb imm)

theorem shld_m32_r32_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM32R32SegEffect p (5 + am.tail.length) base am
        (gprNumber 0 0 reg) (shiftCount 32 imm)) := by
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := shld_m_r_imm8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg) imm
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
      (shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m32_r32_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 4 (5 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM32R32SegEffect p (5 + am.tail.length) base am
        (gprNumber 0 0 reg) (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM32R32SegEffect_components]; exact mem_components_rmw _ _) hpre.store.code
    (by simp; omega))
    (shld_m32_r32_imm8_seg_effect_step p r base reg am hv hx hb imm)

theorem shld_m32_r32_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect (SegRmwPre p r base am 4 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM32R32SegEffect p (6 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 32 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := shld_m_r_imm8_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg) imm
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
      (shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m32_r32_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 4 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM32R32SegEffect p (6 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM32R32SegEffect_components]; exact mem_components_rmw _ _) hpre.store.code
    (by simp; omega))
    (shld_m32_r32_imm8_rex_seg_effect_step p r base rex hrex reg am hv hx hb imm)

theorem shld_m16_r16_imm8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    StepEffect (SegRmwPre p r base am 2 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM16R16SegEffect p (6 + am.tail.length) base am
        (gprNumber 0 0 reg) (shiftCount 16 imm)) := by
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := shld_m16_r16_imm8_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).withSeg hseg) imm
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
      (shldSpec_fst _ _ _ _ hc _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m16_r16_imm8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (SegRmwPre p r base am 2 (6 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM16R16SegEffect p (6 + am.tail.length) base am
        (gprNumber 0 0 reg) (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM16R16SegEffect_components]; exact mem_components_rmw _ _) hpre.store.code
    (by simp; omega))
    (shld_m16_r16_imm8_seg_effect_step p r base reg am hv hx hb imm hc)

theorem shld_m16_r16_imm8_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    StepEffect (SegRmwPre p r base am 2 (7 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM16R16SegEffect p (7 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 16 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hp, hseg, hbase, hread, htables⟩ := segRmw_facts hpre
  subst hbase
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66, rex] =
      withSeg (oszRexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66, rex]
      (noSegPrefix_cons noSegPrefix_66 (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil)), scanContext_66_rex _ _ hr]
  have hstep := shld_m16_r16_imm8_step s h [r.prefixByte, 0x66, rex] (scanPrefix_seg_cons r (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).withSeg hseg) imm
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
      (shldSpec_fst _ _ _ _ hc _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m16_r16_imm8_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (SegRmwPre p r base am 2 (7 + am.tail.length))
      (codeRange p (r.prefixByte :: 0x66 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM16R16SegEffect p (7 + am.tail.length) base am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM16R16SegEffect_components]; exact mem_components_rmw _ _) hpre.store.code
    (by simp; omega))
    (shld_m16_r16_imm8_rex_seg_effect_step p r base rex hrex reg am hv hx hb imm hc)

theorem shld_m64_r64_imm8_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 8 (6 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM64R64A32Effect p (6 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 64 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := shld_m_r_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 64 (.inl rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
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
      (shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m64_r64_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple (Rmw32Pre p am 8 (6 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM64R64A32Effect p (6 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 64 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM64R64A32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m64_r64_imm8_a32_effect_step p rex hrex reg am hv hx hb imm)

theorem shld_m32_r32_imm8_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM32R32A32Effect p (5 + am.tail.length) am
        (gprNumber 0 0 reg) (shiftCount 32 imm)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (5 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := shld_m_r_imm8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz) imm
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
      (shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m32_r32_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) :
    Triple (Rmw32Pre p am 4 (5 + am.tail.length))
      (codeRange p (0x67 :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM32R32A32Effect p (5 + am.tail.length) am
        (gprNumber 0 0 reg) (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM32R32A32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m32_r32_imm8_a32_effect_step p reg am hv hx hb imm)

theorem shld_m32_r32_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    StepEffect (Rmw32Pre p am 4 (6 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM32R32A32Effect p (6 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 32 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := shld_m_r_imm8_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp) 32 (.inr rfl)
    (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz) imm
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
      (shldSpec_fst _ _ _ _ (by unfold shiftCount; split <;> omega) _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m32_r32_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) :
    Triple (Rmw32Pre p am 4 (6 + am.tail.length))
      (codeRange p (0x67 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM32R32A32Effect p (6 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 32 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM32R32A32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m32_r32_imm8_rex_a32_effect_step p rex hrex reg am hv hx hb imm)

theorem shld_m16_r16_imm8_a32_effect_step [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    StepEffect (Rmw32Pre p am 2 (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM16R16A32Effect p (6 + am.tail.length) am
        (gprNumber 0 0 reg) (shiftCount 16 imm)) := by
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (6 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := shld_m16_r16_imm8_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    (by rw [hsc]; exact rfl)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.osz _ am hx hb).toSeg.withAsz) imm
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
      (shldSpec_fst _ _ _ _ hc _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m16_r16_imm8_a32_triple_of_bytes [Bindings] (p : BitVec 64)
    (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : am.rexX = 0) (hb : am.rexB = 0)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (Rmw32Pre p am 2 (6 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM16R16A32Effect p (6 + am.tail.length) am
        (gprNumber 0 0 reg) (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM16R16A32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m16_r16_imm8_a32_effect_step p reg am hv hx hb imm hc)

theorem shld_m16_r16_imm8_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    StepEffect (Rmw32Pre p am 2 (7 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (shldM16R16A32Effect p (7 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 16 imm)) := by
  have hr := hrex.rexPrefix
  intro s h hcode hpre
  obtain ⟨hread, htables⟩ := rmw32_facts hpre
  obtain ⟨hp, -⟩ := hpre
  subst hp
  have hlow : s.RIP.toNat + (7 + am.tail.length) ≤ 2^32 := by
    have := am.tail_length_le
    have := hcode.low (by simp) (by simp; omega)
    simp only [List.length_cons, List.length_append, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66, rex] =
      withAsz (oszRexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_66_rex _ _ hr]
  have hstep := shld_m16_r16_imm8_a32_step s h [0x67, 0x66, rex] (scanPrefix_asz_cons (by simp [scanPrefix_66, hr.scanPrefix])) (by simp)
    (by rw [hsc]; exact hrex.operand_size_osz s.DS)
    (by rw [hsc]; rfl) (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) reg am hv
    (by rw [hsc]; exact (AddrContext.oszRex _ _ am hx hb).toSeg.withAsz) imm
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
      (shldSpec_fst _ _ _ _ hc _ _)
  · exact shldFlags_allows _ _ _ _ _ _

theorem shld_m16_r16_imm8_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (reg : BitVec 3) (am : AddrMode) (hv : am.Valid)
    (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (Rmw32Pre p am 2 (7 + am.tail.length))
      (codeRange p (0x67 :: 0x66 :: rex :: 0x0F :: 0xA4 :: am.modrm reg :: (am.tail ++ immBytes 8 imm)))
      (Effect.post (shldM16R16A32Effect p (7 + am.tail.length) am
        (gprNumber 0 (rexR rex.toBitVec) reg) (shiftCount 16 imm))) :=
  Triple.of_effect (fun s hpre => Effect.avoids_of_mem
    (by rw [shldM16R16A32Effect_components]; exact mem_components_rmw _ _) hpre.code
    (by simp; omega))
    (shld_m16_r16_imm8_rex_a32_effect_step p rex hrex reg am hv hx hb imm hc)

theorem shld_m64_r64_imm8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple (RmwPre p am 8 (encodeShldM64R64Imm8 src am imm).length)
      (codeRange p (encodeShldM64R64Imm8 src am imm))
      (Effect.post
        (shldM64R64Effect p (encodeShldM64R64Imm8 src am imm).length am
          (src.setWidth 5) (shiftCount 64 imm))) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := shld_m64_r64_imm8_triple_of_bytes p _ hrex (regLow src) am hv hx hb imm
  rw [hr, gprNumber_reg] at this
  unfold encodeShldM64R64Imm8
  rw [show (am.rexByte true src :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)).length =
    5 + am.tail.length by simp; omega]
  exact this

theorem shld_m32_r32_imm8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple (RmwPre p am 4 (encodeShldM32R32Imm8 src am imm).length)
      (codeRange p (encodeShldM32R32Imm8 src am imm))
      (Effect.post
        (shldM32R32Effect p (encodeShldM32R32Imm8 src am imm).length am
          (src.setWidth 5) (shiftCount 32 imm))) := by
  unfold encodeShldM32R32Imm8
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shld_m32_r32_imm8_triple_of_bytes p (regLow src) am hv hx hb imm
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)).length =
      4 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shld_m32_r32_imm8_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb imm
    rw [hr, gprNumber_reg] at this
    rw [show (am.rexByte false src :: 0x0F :: 0xA4 :: am.modrm (regLow src) ::
      (am.tail ++ immBytes 8 imm)).length = 5 + am.tail.length by simp; omega]
    exact this

theorem shld_m16_r16_imm8_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (RmwPre p am 2 (encodeShldM16R16Imm8 src am imm).length)
      (codeRange p (encodeShldM16R16Imm8 src am imm))
      (Effect.post
        (shldM16R16Effect p (encodeShldM16R16Imm8 src am imm).length am
          (src.setWidth 5) (shiftCount 16 imm))) := by
  unfold encodeShldM16R16Imm8
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shld_m16_r16_imm8_triple_of_bytes p (regLow src) am hv hx hb imm hc
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (0x66 :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shld_m16_r16_imm8_rex_triple_of_bytes p _ hrex (regLow src) am hv hx hb imm hc
    rw [hr, gprNumber_reg] at this
    rw [show (0x66 :: am.rexByte false src :: 0x0F :: 0xA4 :: am.modrm (regLow src) ::
      (am.tail ++ immBytes 8 imm)).length = 6 + am.tail.length by simp; omega]
    exact this

theorem shld_m64_r64_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 8 (r.prefixByte :: encodeShldM64R64Imm8 src am imm).length)
      (codeRange p (r.prefixByte :: encodeShldM64R64Imm8 src am imm))
      (Effect.post
        (shldM64R64SegEffect p (r.prefixByte :: encodeShldM64R64Imm8 src am imm).length base am
          (src.setWidth 5) (shiftCount 64 imm))) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := shld_m64_r64_imm8_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb imm
  rw [hr, gprNumber_reg] at this
  unfold encodeShldM64R64Imm8
  rw [show (r.prefixByte :: am.rexByte true src :: 0x0F :: 0xA4 :: am.modrm (regLow src) ::
    (am.tail ++ immBytes 8 imm)).length = 6 + am.tail.length by simp; omega]
  exact this

theorem shld_m32_r32_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) :
    Triple (SegRmwPre p r base am 4 (r.prefixByte :: encodeShldM32R32Imm8 src am imm).length)
      (codeRange p (r.prefixByte :: encodeShldM32R32Imm8 src am imm))
      (Effect.post
        (shldM32R32SegEffect p (r.prefixByte :: encodeShldM32R32Imm8 src am imm).length base am
          (src.setWidth 5) (shiftCount 32 imm))) := by
  unfold encodeShldM32R32Imm8
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shld_m32_r32_imm8_seg_triple_of_bytes p r base (regLow src) am hv hx hb imm
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (r.prefixByte :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shld_m32_r32_imm8_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb imm
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: am.rexByte false src :: 0x0F :: 0xA4 :: am.modrm (regLow src) ::
      (am.tail ++ immBytes 8 imm)).length = 6 + am.tail.length by simp; omega]
    exact this

theorem shld_m16_r16_imm8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (src : BitVec 4) (am : AddrMode) (hv : am.Valid) (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (SegRmwPre p r base am 2 (r.prefixByte :: encodeShldM16R16Imm8 src am imm).length)
      (codeRange p (r.prefixByte :: encodeShldM16R16Imm8 src am imm))
      (Effect.post
        (shldM16R16SegEffect p (r.prefixByte :: encodeShldM16R16Imm8 src am imm).length base am
          (src.setWidth 5) (shiftCount 16 imm))) := by
  unfold encodeShldM16R16Imm8
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shld_m16_r16_imm8_seg_triple_of_bytes p r base (regLow src) am hv hx hb imm hc
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (r.prefixByte :: 0x66 :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)).length =
      6 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shld_m16_r16_imm8_rex_seg_triple_of_bytes p r base _ hrex (regLow src) am hv hx hb imm hc
    rw [hr, gprNumber_reg] at this
    rw [show (r.prefixByte :: 0x66 :: am.rexByte false src :: 0x0F :: 0xA4 :: am.modrm (regLow src) ::
      (am.tail ++ immBytes 8 imm)).length = 7 + am.tail.length by simp; omega]
    exact this

theorem shld_m64_r64_imm8_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 8 (0x67 :: encodeShldM64R64Imm8 src am imm).length)
      (codeRange p (0x67 :: encodeShldM64R64Imm8 src am imm))
      (Effect.post
        (shldM64R64A32Effect p (0x67 :: encodeShldM64R64Imm8 src am imm).length am (src.setWidth 5) (shiftCount 64 imm))) := by
  obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_true_spec src
  have := shld_m64_r64_imm8_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb imm
  rw [hr, gprNumber_reg] at this
  unfold encodeShldM64R64Imm8
  rw [show (0x67 :: am.rexByte true src :: 0x0F :: 0xA4 :: am.modrm (regLow src) ::
    (am.tail ++ immBytes 8 imm)).length = 6 + am.tail.length by simp; omega]
  exact this

theorem shld_m32_r32_imm8_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) :
    Triple (Rmw32Pre p am 4 (0x67 :: encodeShldM32R32Imm8 src am imm).length)
      (codeRange p (0x67 :: encodeShldM32R32Imm8 src am imm))
      (Effect.post
        (shldM32R32A32Effect p (0x67 :: encodeShldM32R32Imm8 src am imm).length am (src.setWidth 5) (shiftCount 32 imm))) := by
  unfold encodeShldM32R32Imm8
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shld_m32_r32_imm8_a32_triple_of_bytes p (regLow src) am hv hx hb imm
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (0x67 :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)).length =
      5 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shld_m32_r32_imm8_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb imm
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: am.rexByte false src :: 0x0F :: 0xA4 :: am.modrm (regLow src) ::
      (am.tail ++ immBytes 8 imm)).length = 6 + am.tail.length by simp; omega]
    exact this

theorem shld_m16_r16_imm8_a32_triple [Bindings] (p : BitVec 64) (src : BitVec 4) (am : AddrMode)
    (hv : am.Valid) (imm : BitVec 8) (hc : shiftCount 16 imm ≤ 16) :
    Triple (Rmw32Pre p am 2 (0x67 :: encodeShldM16R16Imm8 src am imm).length)
      (codeRange p (0x67 :: encodeShldM16R16Imm8 src am imm))
      (Effect.post
        (shldM16R16A32Effect p (0x67 :: encodeShldM16R16Imm8 src am imm).length am (src.setWidth 5) (shiftCount 16 imm))) := by
  unfold encodeShldM16R16Imm8
  split
  · rename_i hc'
    obtain ⟨hr, hx, hb⟩ := hc'
    have := shld_m16_r16_imm8_a32_triple_of_bytes p (regLow src) am hv hx hb imm hc
    rw [show gprNumber 0 0 (regLow src) = src.setWidth 5 by rw [← gprNumber_reg src, hr]] at this
    rw [show (0x67 :: 0x66 :: 0x0F :: 0xA4 :: am.modrm (regLow src) :: (am.tail ++ immBytes 8 imm)).length =
      6 + am.tail.length by simp; omega]
    exact this
  · obtain ⟨hrex, hr, hx, hb⟩ := am.rexByte_false_spec src
    have := shld_m16_r16_imm8_rex_a32_triple_of_bytes p _ hrex (regLow src) am hv hx hb imm hc
    rw [hr, gprNumber_reg] at this
    rw [show (0x67 :: 0x66 :: am.rexByte false src :: 0x0F :: 0xA4 :: am.modrm (regLow src) ::
      (am.tail ++ immBytes 8 imm)).length = 7 + am.tail.length by simp; omega]
    exact this

attribute [x86_compose] shldM64R64Effect shldM32R32Effect shldM16R16Effect shldM64R64SegEffect shldM32R32SegEffect shldM16R16SegEffect shldM64R64A32Effect shldM32R32A32Effect shldM16R16A32Effect

@[x86_local] theorem shldM64R64Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} {c : Nat} :
    Effect.Local (shldM64R64Effect p len am src c) := by
  effect_local [shldM64R64Effect, shldFlags]

@[x86_local] theorem shldM64R64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {src : BitVec 5} {c : Nat} :
    Effect.Local (shldM64R64SegEffect p len base am src c) := by
  effect_local [shldM64R64SegEffect, shldFlags]

@[x86_local] theorem shldM64R64A32Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} {c : Nat} :
    Effect.Local (shldM64R64A32Effect p len am src c) := by
  effect_local [shldM64R64A32Effect, shldFlags]

@[x86_local] theorem shldM32R32Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} {c : Nat} :
    Effect.Local (shldM32R32Effect p len am src c) := by
  effect_local [shldM32R32Effect, shldFlags]

@[x86_local] theorem shldM32R32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {src : BitVec 5} {c : Nat} :
    Effect.Local (shldM32R32SegEffect p len base am src c) := by
  effect_local [shldM32R32SegEffect, shldFlags]

@[x86_local] theorem shldM32R32A32Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} {c : Nat} :
    Effect.Local (shldM32R32A32Effect p len am src c) := by
  effect_local [shldM32R32A32Effect, shldFlags]

@[x86_local] theorem shldM16R16Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} {c : Nat} :
    Effect.Local (shldM16R16Effect p len am src c) := by
  effect_local [shldM16R16Effect, shldFlags]

@[x86_local] theorem shldM16R16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {src : BitVec 5} {c : Nat} :
    Effect.Local (shldM16R16SegEffect p len base am src c) := by
  effect_local [shldM16R16SegEffect, shldFlags]

@[x86_local] theorem shldM16R16A32Effect_local {p : BitVec 64} {len : Nat}
    {am : AddrMode} {src : BitVec 5} {c : Nat} :
    Effect.Local (shldM16R16A32Effect p len am src c) := by
  effect_local [shldM16R16A32Effect, shldFlags]

end X86Proofs
