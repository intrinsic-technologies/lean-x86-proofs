import X86Proofs.Instructions.Mov.Generated.MoffsStore.Step
import X86Proofs.Instructions.Mov.Generated.MoffsStore.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movMoffs64RaxEffect (p : BitVec 64) (len : Nat) (moffs : BitVec 64) : RamState → Effect :=
  storeEffect p len (fun _ => moffs) fun s => (Operand.reg 0 : Operand 64).read s

def movMoffs64RaxSegEffect (p : BitVec 64) (len : Nat) (base moffs : BitVec 64) : RamState → Effect :=
  storeEffect p len (fun _ => base + moffs) fun s => (Operand.reg 0 : Operand 64).read s

def movMoffs32EaxEffect (p : BitVec 64) (len : Nat) (moffs : BitVec 64) : RamState → Effect :=
  storeEffect p len (fun _ => moffs) fun s => (Operand.reg 0 : Operand 32).read s

def movMoffs32EaxSegEffect (p : BitVec 64) (len : Nat) (base moffs : BitVec 64) : RamState → Effect :=
  storeEffect p len (fun _ => base + moffs) fun s => (Operand.reg 0 : Operand 32).read s

def movMoffs16AxEffect (p : BitVec 64) (len : Nat) (moffs : BitVec 64) : RamState → Effect :=
  storeEffect p len (fun _ => moffs) fun s => (Operand.reg 0 : Operand 16).read s

def movMoffs16AxSegEffect (p : BitVec 64) (len : Nat) (base moffs : BitVec 64) : RamState → Effect :=
  storeEffect p len (fun _ => base + moffs) fun s => (Operand.reg 0 : Operand 16).read s

def movMoffs8AlEffect (p : BitVec 64) (len : Nat) (moffs : BitVec 64) : RamState → Effect :=
  storeEffect p len (fun _ => moffs) fun s => (Operand.reg 0 : Operand 8).read s

def movMoffs8AlSegEffect (p : BitVec 64) (len : Nat) (base moffs : BitVec 64) : RamState → Effect :=
  storeEffect p len (fun _ => base + moffs) fun s => (Operand.reg 0 : Operand 8).read s

theorem mov_moffs64_rax_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 64) :
    StepEffect (StorePre p 10 (fun _ => moffs) 8)
      (codeRange p (rex :: 0xA3 :: immBytes 64 moffs))
      (movMoffs64RaxEffect p 10 moffs) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + 10 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_moffs_rax_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    64 (.inl rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; exact MoffsContext.toSeg ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) moffs hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hw)
  simp only [scanContext_rex _ _ hr] at hstep
  rw [show segAddr (rexContext s.DS rex.toBitVec) moffs = moffs from rfl] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs64_rax_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 64) :
    Triple (StorePre p 10 (fun _ => moffs) 8)
      (codeRange p (rex :: 0xA3 :: immBytes 64 moffs))
      (Effect.post (movMoffs64RaxEffect p 10 moffs)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre)
    (mov_moffs64_rax_effect_step p rex hrex moffs)

theorem mov_moffs64_rax_triple [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (StorePre p 10 (fun _ => moffs) 8)
      (codeRange p (encodeMovMoffs64Rax moffs))
      (Effect.post (movMoffs64RaxEffect p 10 moffs)) :=
  mov_moffs64_rax_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide) moffs

theorem mov_moffs32_eax_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    StepEffect (StorePre p 9 (fun _ => moffs) 4)
      (codeRange p (0xA3 :: immBytes 64 moffs))
      (movMoffs32EaxEffect p 9 moffs) := by
  refine StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + 9 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_moffs_rax_step s h [] (by simp) (by simp)
    32 (.inr (.inl rfl)) (by exact rfl)
    (by exact MoffsContext.toSeg ⟨rfl, rfl, rfl, rfl⟩)
    (by rfl)
    (by rfl) moffs hcode.bytesAt hlow (by exact hw)
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) []) moffs = moffs from rfl] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs32_eax_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (StorePre p 9 (fun _ => moffs) 4)
      (codeRange p (0xA3 :: immBytes 64 moffs))
      (Effect.post (movMoffs32EaxEffect p 9 moffs)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre)
    (mov_moffs32_eax_effect_step p moffs)

theorem mov_moffs32_eax_triple [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (StorePre p 9 (fun _ => moffs) 4)
      (codeRange p (encodeMovMoffs32Eax moffs))
      (Effect.post (movMoffs32EaxEffect p 9 moffs)) :=
  mov_moffs32_eax_triple_of_bytes p moffs

theorem mov_moffs16_ax_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    StepEffect (StorePre p 10 (fun _ => moffs) 2)
      (codeRange p (0x66 :: 0xA3 :: immBytes 64 moffs))
      (movMoffs16AxEffect p 10 moffs) := by
  refine StepEffect.of_store (n := 16) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + 10 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_moffs_rax_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    16 (.inr (.inr rfl)) (by exact rfl)
    (by exact MoffsContext.toSeg ⟨rfl, rfl, rfl, rfl⟩)
    (by rfl)
    (by rfl) moffs hcode.bytesAt hlow (by exact hw)
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) [0x66]) moffs = moffs from rfl] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs16_ax_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (StorePre p 10 (fun _ => moffs) 2)
      (codeRange p (0x66 :: 0xA3 :: immBytes 64 moffs))
      (Effect.post (movMoffs16AxEffect p 10 moffs)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre)
    (mov_moffs16_ax_effect_step p moffs)

theorem mov_moffs16_ax_triple [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (StorePre p 10 (fun _ => moffs) 2)
      (codeRange p (encodeMovMoffs16Ax moffs))
      (Effect.post (movMoffs16AxEffect p 10 moffs)) :=
  mov_moffs16_ax_triple_of_bytes p moffs

theorem mov_moffs8_al_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    StepEffect (StorePre p 9 (fun _ => moffs) 1)
      (codeRange p (0xA2 :: immBytes 64 moffs))
      (movMoffs8AlEffect p 9 moffs) := by
  refine StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + 9 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_moffs8_al_step s h [] (by simp) (by simp)
    (by exact MoffsContext.toSeg ⟨rfl, rfl, rfl, rfl⟩)
    (by rfl)
    (by rfl) moffs hcode.bytesAt hlow (by exact hw)
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) []) moffs = moffs from rfl] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs8_al_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (StorePre p 9 (fun _ => moffs) 1)
      (codeRange p (0xA2 :: immBytes 64 moffs))
      (Effect.post (movMoffs8AlEffect p 9 moffs)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre)
    (mov_moffs8_al_effect_step p moffs)

theorem mov_moffs8_al_triple [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (StorePre p 9 (fun _ => moffs) 1)
      (codeRange p (encodeMovMoffs8Al moffs))
      (Effect.post (movMoffs8AlEffect p 9 moffs)) :=
  mov_moffs8_al_triple_of_bytes p moffs

theorem mov_moffs64_rax_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 64) :
    StepEffect (SegStorePre p 11 r base (fun _ => moffs) 8)
      (codeRange p (r.prefixByte :: rex :: 0xA3 :: immBytes 64 moffs))
      (movMoffs64RaxSegEffect p 11 base moffs) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_store_pre (n := 64) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode ⟨⟨hp, hw, _⟩, hseg, hbase⟩ => ?_
  subst hp hbase
  have hlow : s.RIP.toNat + 11 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := mov_moffs_rax_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    64 (.inl rfl) (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; exact MoffsContext.withSeg ⟨rfl, rfl, rfl, rfl⟩ hseg)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs64_rax_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 64) :
    Triple (SegStorePre p 11 r base (fun _ => moffs) 8)
      (codeRange p (r.prefixByte :: rex :: 0xA3 :: immBytes 64 moffs))
      (Effect.post (movMoffs64RaxSegEffect p 11 base moffs)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre.store)
    (mov_moffs64_rax_seg_effect_step p r base rex hrex moffs)

theorem mov_moffs64_rax_seg_triple [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegStorePre p 11 r base (fun _ => moffs) 8)
      (codeRange p (r.prefixByte :: encodeMovMoffs64Rax moffs))
      (Effect.post (movMoffs64RaxSegEffect p 11 base moffs)) :=
  mov_moffs64_rax_seg_triple_of_bytes p r base 0x48 (by unfold RexWPrefix; decide) moffs

theorem mov_moffs32_eax_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    StepEffect (SegStorePre p 10 r base (fun _ => moffs) 4)
      (codeRange p (r.prefixByte :: 0xA3 :: immBytes 64 moffs))
      (movMoffs32EaxSegEffect p 10 base moffs) := by
  refine StepEffect.of_store_pre (n := 32) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode ⟨⟨hp, hw, _⟩, hseg, hbase⟩ => ?_
  subst hp hbase
  have hlow : s.RIP.toNat + 10 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := mov_moffs_rax_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    32 (.inr (.inl rfl)) (by rw [hsc]; exact rfl)
    (by rw [hsc]; exact MoffsContext.withSeg ⟨rfl, rfl, rfl, rfl⟩ hseg)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs32_eax_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegStorePre p 10 r base (fun _ => moffs) 4)
      (codeRange p (r.prefixByte :: 0xA3 :: immBytes 64 moffs))
      (Effect.post (movMoffs32EaxSegEffect p 10 base moffs)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre.store)
    (mov_moffs32_eax_seg_effect_step p r base moffs)

theorem mov_moffs32_eax_seg_triple [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegStorePre p 10 r base (fun _ => moffs) 4)
      (codeRange p (r.prefixByte :: encodeMovMoffs32Eax moffs))
      (Effect.post (movMoffs32EaxSegEffect p 10 base moffs)) :=
  mov_moffs32_eax_seg_triple_of_bytes p r base moffs

theorem mov_moffs16_ax_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    StepEffect (SegStorePre p 11 r base (fun _ => moffs) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xA3 :: immBytes 64 moffs))
      (movMoffs16AxSegEffect p 11 base moffs) := by
  refine StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode ⟨⟨hp, hw, _⟩, hseg, hbase⟩ => ?_
  subst hp hbase
  have hlow : s.RIP.toNat + 11 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := mov_moffs_rax_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    16 (.inr (.inr rfl)) (by rw [hsc]; exact rfl)
    (by rw [hsc]; exact MoffsContext.withSeg ⟨rfl, rfl, rfl, rfl⟩ hseg)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs16_ax_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegStorePre p 11 r base (fun _ => moffs) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xA3 :: immBytes 64 moffs))
      (Effect.post (movMoffs16AxSegEffect p 11 base moffs)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre.store)
    (mov_moffs16_ax_seg_effect_step p r base moffs)

theorem mov_moffs16_ax_seg_triple [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegStorePre p 11 r base (fun _ => moffs) 2)
      (codeRange p (r.prefixByte :: encodeMovMoffs16Ax moffs))
      (Effect.post (movMoffs16AxSegEffect p 11 base moffs)) :=
  mov_moffs16_ax_seg_triple_of_bytes p r base moffs

theorem mov_moffs8_al_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    StepEffect (SegStorePre p 10 r base (fun _ => moffs) 1)
      (codeRange p (r.prefixByte :: 0xA2 :: immBytes 64 moffs))
      (movMoffs8AlSegEffect p 10 base moffs) := by
  refine StepEffect.of_store_pre (n := 8) (by decide) (by decide) _ _ (fun _ hs => hs.store)
    fun s h hcode ⟨⟨hp, hw, _⟩, hseg, hbase⟩ => ?_
  subst hp hbase
  have hlow : s.RIP.toNat + 10 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := mov_moffs8_al_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; exact MoffsContext.withSeg ⟨rfl, rfl, rfl, rfl⟩ hseg)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
  simp only [hsc, segAddr_withSeg] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs8_al_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegStorePre p 10 r base (fun _ => moffs) 1)
      (codeRange p (r.prefixByte :: 0xA2 :: immBytes 64 moffs))
      (Effect.post (movMoffs8AlSegEffect p 10 base moffs)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre.store)
    (mov_moffs8_al_seg_effect_step p r base moffs)

theorem mov_moffs8_al_seg_triple [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegStorePre p 10 r base (fun _ => moffs) 1)
      (codeRange p (r.prefixByte :: encodeMovMoffs8Al moffs))
      (Effect.post (movMoffs8AlSegEffect p 10 base moffs)) :=
  mov_moffs8_al_seg_triple_of_bytes p r base moffs

theorem mov_moffs64_rax_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 32) :
    StepEffect (StorePre p 7 (fun _ => (moffs.setWidth 64)) 8)
      (codeRange p (0x67 :: rex :: 0xA3 :: immBytes 32 moffs))
      (movMoffs64RaxEffect p 7 (moffs.setWidth 64)) := by
  have hr := hrex.rexPrefix
  refine StepEffect.of_store (n := 64) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + 7 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := mov_moffs_rax_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    64 (.inl rfl) (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; exact MoffsContext.withAsz ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc]; exact hw)
  simp only [hsc] at hstep
  rw [show segAddr (withAsz (rexContext s.DS rex.toBitVec)) (moffs.setWidth 64) = (moffs.setWidth 64) from rfl] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs64_rax_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 32) :
    Triple (StorePre p 7 (fun _ => (moffs.setWidth 64)) 8)
      (codeRange p (0x67 :: rex :: 0xA3 :: immBytes 32 moffs))
      (Effect.post (movMoffs64RaxEffect p 7 (moffs.setWidth 64))) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre)
    (mov_moffs64_rax_a32_effect_step p rex hrex moffs)

theorem mov_moffs64_rax_a32_triple [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (StorePre p 7 (fun _ => (moffs.setWidth 64)) 8)
      (codeRange p (encodeMovMoffs64RaxA32 moffs))
      (Effect.post (movMoffs64RaxEffect p 7 (moffs.setWidth 64))) :=
  mov_moffs64_rax_a32_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide) moffs

theorem mov_moffs32_eax_a32_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    StepEffect (StorePre p 6 (fun _ => (moffs.setWidth 64)) 4)
      (codeRange p (0x67 :: 0xA3 :: immBytes 32 moffs))
      (movMoffs32EaxEffect p 6 (moffs.setWidth 64)) := by
  refine StepEffect.of_store (n := 32) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := mov_moffs_rax_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    32 (.inr (.inl rfl)) (by rw [hsc]; exact rfl)
    (by rw [hsc]; exact MoffsContext.withAsz ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc]; exact hw)
  simp only [hsc] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])) (moffs.setWidth 64) = (moffs.setWidth 64) from rfl] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs32_eax_a32_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (StorePre p 6 (fun _ => (moffs.setWidth 64)) 4)
      (codeRange p (0x67 :: 0xA3 :: immBytes 32 moffs))
      (Effect.post (movMoffs32EaxEffect p 6 (moffs.setWidth 64))) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre)
    (mov_moffs32_eax_a32_effect_step p moffs)

theorem mov_moffs32_eax_a32_triple [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (StorePre p 6 (fun _ => (moffs.setWidth 64)) 4)
      (codeRange p (encodeMovMoffs32EaxA32 moffs))
      (Effect.post (movMoffs32EaxEffect p 6 (moffs.setWidth 64))) :=
  mov_moffs32_eax_a32_triple_of_bytes p moffs

theorem mov_moffs16_ax_a32_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    StepEffect (StorePre p 7 (fun _ => (moffs.setWidth 64)) 2)
      (codeRange p (0x67 :: 0x66 :: 0xA3 :: immBytes 32 moffs))
      (movMoffs16AxEffect p 7 (moffs.setWidth 64)) := by
  refine StepEffect.of_store (n := 16) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + 7 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := mov_moffs_rax_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    16 (.inr (.inr rfl)) (by rw [hsc]; exact rfl)
    (by rw [hsc]; exact MoffsContext.withAsz ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc]; exact hw)
  simp only [hsc] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])) (moffs.setWidth 64) = (moffs.setWidth 64) from rfl] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs16_ax_a32_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (StorePre p 7 (fun _ => (moffs.setWidth 64)) 2)
      (codeRange p (0x67 :: 0x66 :: 0xA3 :: immBytes 32 moffs))
      (Effect.post (movMoffs16AxEffect p 7 (moffs.setWidth 64))) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre)
    (mov_moffs16_ax_a32_effect_step p moffs)

theorem mov_moffs16_ax_a32_triple [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (StorePre p 7 (fun _ => (moffs.setWidth 64)) 2)
      (codeRange p (encodeMovMoffs16AxA32 moffs))
      (Effect.post (movMoffs16AxEffect p 7 (moffs.setWidth 64))) :=
  mov_moffs16_ax_a32_triple_of_bytes p moffs

theorem mov_moffs8_al_a32_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    StepEffect (StorePre p 6 (fun _ => (moffs.setWidth 64)) 1)
      (codeRange p (0x67 :: 0xA2 :: immBytes 32 moffs))
      (movMoffs8AlEffect p 6 (moffs.setWidth 64)) := by
  refine StepEffect.of_store (n := 8) (by decide) (by decide) _ _
    fun s h hcode ⟨hp, hw, _⟩ => ?_
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := mov_moffs8_al_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; exact MoffsContext.withAsz ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc]; exact hw)
  simp only [hsc] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])) (moffs.setWidth 64) = (moffs.setWidth 64) from rfl] at hstep
  simp only [movSpec] at hstep
  exact hstep

theorem mov_moffs8_al_a32_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (StorePre p 6 (fun _ => (moffs.setWidth 64)) 1)
      (codeRange p (0x67 :: 0xA2 :: immBytes 32 moffs))
      (Effect.post (movMoffs8AlEffect p 6 (moffs.setWidth 64))) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp) _ _ hpre)
    (mov_moffs8_al_a32_effect_step p moffs)

theorem mov_moffs8_al_a32_triple [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (StorePre p 6 (fun _ => (moffs.setWidth 64)) 1)
      (codeRange p (encodeMovMoffs8AlA32 moffs))
      (Effect.post (movMoffs8AlEffect p 6 (moffs.setWidth 64))) :=
  mov_moffs8_al_a32_triple_of_bytes p moffs

attribute [x86_compose] movMoffs64RaxEffect movMoffs64RaxSegEffect movMoffs32EaxEffect movMoffs32EaxSegEffect movMoffs16AxEffect movMoffs16AxSegEffect movMoffs8AlEffect movMoffs8AlSegEffect

@[x86_local] theorem movMoffs64RaxEffect_local {p : BitVec 64} {len : Nat} {moffs : BitVec 64} :
    Effect.Local (movMoffs64RaxEffect p len moffs) := by
  effect_local [movMoffs64RaxEffect, storeEffect]

@[x86_local] theorem movMoffs64RaxSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {moffs : BitVec 64} :
    Effect.Local (movMoffs64RaxSegEffect p len base moffs) := by
  effect_local [movMoffs64RaxSegEffect, storeEffect]

@[x86_local] theorem movMoffs32EaxEffect_local {p : BitVec 64} {len : Nat} {moffs : BitVec 64} :
    Effect.Local (movMoffs32EaxEffect p len moffs) := by
  effect_local [movMoffs32EaxEffect, storeEffect]

@[x86_local] theorem movMoffs32EaxSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {moffs : BitVec 64} :
    Effect.Local (movMoffs32EaxSegEffect p len base moffs) := by
  effect_local [movMoffs32EaxSegEffect, storeEffect]

@[x86_local] theorem movMoffs16AxEffect_local {p : BitVec 64} {len : Nat} {moffs : BitVec 64} :
    Effect.Local (movMoffs16AxEffect p len moffs) := by
  effect_local [movMoffs16AxEffect, storeEffect]

@[x86_local] theorem movMoffs16AxSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {moffs : BitVec 64} :
    Effect.Local (movMoffs16AxSegEffect p len base moffs) := by
  effect_local [movMoffs16AxSegEffect, storeEffect]

@[x86_local] theorem movMoffs8AlEffect_local {p : BitVec 64} {len : Nat} {moffs : BitVec 64} :
    Effect.Local (movMoffs8AlEffect p len moffs) := by
  effect_local [movMoffs8AlEffect, storeEffect]

@[x86_local] theorem movMoffs8AlSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {moffs : BitVec 64} :
    Effect.Local (movMoffs8AlSegEffect p len base moffs) := by
  effect_local [movMoffs8AlSegEffect, storeEffect]

end X86Proofs
