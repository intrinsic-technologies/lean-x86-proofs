import X86Proofs.Instructions.Mov.Generated.MoffsLoad.Step
import X86Proofs.Instructions.Mov.Generated.MoffsLoad.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movRaxMoffs64Effect (p : BitVec 64) (len : Nat) (moffs : BitVec 64) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      (Operand.mem moffs : Operand 64).read s⟩] }

@[simp] theorem movRaxMoffs64Effect_components (p : BitVec 64) (len : Nat) (moffs : BitVec 64)
    (s : RamState) : (movRaxMoffs64Effect p len moffs s).components = [.reg 0, .rip] := rfl

def movRaxMoffs64SegEffect (p : BitVec 64) (len : Nat) (base moffs : BitVec 64)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      (Operand.mem (base + moffs) : Operand 64).read s⟩] }

@[simp] theorem movRaxMoffs64SegEffect_components (p : BitVec 64) (len : Nat) (base moffs : BitVec 64)
    (s : RamState) : (movRaxMoffs64SegEffect p len base moffs s).components = [.reg 0, .rip] := rfl

def movEaxMoffs32Effect (p : BitVec 64) (len : Nat) (moffs : BitVec 64) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      ((Operand.mem moffs : Operand 32).read s).setWidth 64⟩] }

@[simp] theorem movEaxMoffs32Effect_components (p : BitVec 64) (len : Nat) (moffs : BitVec 64)
    (s : RamState) : (movEaxMoffs32Effect p len moffs s).components = [.reg 0, .rip] := rfl

def movEaxMoffs32SegEffect (p : BitVec 64) (len : Nat) (base moffs : BitVec 64)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      ((Operand.mem (base + moffs) : Operand 32).read s).setWidth 64⟩] }

@[simp] theorem movEaxMoffs32SegEffect_components (p : BitVec 64) (len : Nat) (base moffs : BitVec 64)
    (s : RamState) : (movEaxMoffs32SegEffect p len base moffs s).components = [.reg 0, .rip] := rfl

def movAxMoffs16Effect (p : BitVec 64) (len : Nat) (moffs : BitVec 64) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 ((Operand.mem moffs : Operand 16).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩] }

@[simp] theorem movAxMoffs16Effect_components (p : BitVec 64) (len : Nat) (moffs : BitVec 64)
    (s : RamState) : (movAxMoffs16Effect p len moffs s).components = [.reg 0, .rip] := rfl

def movAxMoffs16SegEffect (p : BitVec 64) (len : Nat) (base moffs : BitVec 64)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 16 ((Operand.mem (base + moffs) : Operand 16).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩] }

@[simp] theorem movAxMoffs16SegEffect_components (p : BitVec 64) (len : Nat) (base moffs : BitVec 64)
    (s : RamState) : (movAxMoffs16SegEffect p len base moffs s).components = [.reg 0, .rip] := rfl

def movAlMoffs8Effect (p : BitVec 64) (len : Nat) (moffs : BitVec 64) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 ((Operand.mem moffs : Operand 8).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩] }

@[simp] theorem movAlMoffs8Effect_components (p : BitVec 64) (len : Nat) (moffs : BitVec 64)
    (s : RamState) : (movAlMoffs8Effect p len moffs s).components = [.reg 0, .rip] := rfl

def movAlMoffs8SegEffect (p : BitVec 64) (len : Nat) (base moffs : BitVec 64)
    (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg 0 : Operand 64),
      mergeGPR 8 ((Operand.mem (base + moffs) : Operand 8).read s)
        ((Operand.reg 0 : Operand 64).read s)⟩] }

@[simp] theorem movAlMoffs8SegEffect_components (p : BitVec 64) (len : Nat) (base moffs : BitVec 64)
    (s : RamState) : (movAlMoffs8SegEffect p len base moffs s).components = [.reg 0, .rip] := rfl

theorem mov_rax_moffs64_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 64) :
    StepEffect (LoadPre p (fun _ => moffs) 8)
      (codeRange p (rex :: 0xA1 :: immBytes 64 moffs))
      (movRaxMoffs64Effect p 10 moffs) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 10 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_rax_moffs_step s h [rex] (by simpa using hr.scanPrefix) (by simp)
    64 (.inl rfl) (by rw [scanContext_rex _ _ hr]; exact hrex.operand_size s.DS)
    (by rw [scanContext_rex _ _ hr]; exact MoffsContext.toSeg ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [scanContext_rex _ _ hr]; rfl)
    (by rw [scanContext_rex _ _ hr]; rfl) moffs hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hread)
  simp only [scanContext_rex _ _ hr] at hstep
  rw [show segAddr (rexContext s.DS rex.toBitVec) moffs = moffs from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movSpec]

theorem mov_rax_moffs64_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 64) :
    Triple (LoadPre p (fun _ => moffs) 8)
      (codeRange p (rex :: 0xA1 :: immBytes 64 moffs))
      (Effect.post (movRaxMoffs64Effect p 10 moffs)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movRaxMoffs64Effect_components]; simp [Component.Covers]) _)
    (mov_rax_moffs64_effect_step p rex hrex moffs)

theorem mov_rax_moffs64_triple [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (LoadPre p (fun _ => moffs) 8)
      (codeRange p (encodeMovRaxMoffs64 moffs))
      (Effect.post (movRaxMoffs64Effect p 10 moffs)) :=
  mov_rax_moffs64_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide) moffs

theorem mov_eax_moffs32_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    StepEffect (LoadPre p (fun _ => moffs) 4)
      (codeRange p (0xA1 :: immBytes 64 moffs))
      (movEaxMoffs32Effect p 9 moffs) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 9 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_rax_moffs_step s h [] (by simp) (by simp)
    32 (.inr (.inl rfl)) (by exact rfl)
    (by exact MoffsContext.toSeg ⟨rfl, rfl, rfl, rfl⟩)
    (by rfl)
    (by rfl) moffs hcode.bytesAt hlow (by exact hread)
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) []) moffs = moffs from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec]

theorem mov_eax_moffs32_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (LoadPre p (fun _ => moffs) 4)
      (codeRange p (0xA1 :: immBytes 64 moffs))
      (Effect.post (movEaxMoffs32Effect p 9 moffs)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movEaxMoffs32Effect_components]; simp [Component.Covers]) _)
    (mov_eax_moffs32_effect_step p moffs)

theorem mov_eax_moffs32_triple [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (LoadPre p (fun _ => moffs) 4)
      (codeRange p (encodeMovEaxMoffs32 moffs))
      (Effect.post (movEaxMoffs32Effect p 9 moffs)) :=
  mov_eax_moffs32_triple_of_bytes p moffs

theorem mov_ax_moffs16_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    StepEffect (LoadPre p (fun _ => moffs) 2)
      (codeRange p (0x66 :: 0xA1 :: immBytes 64 moffs))
      (movAxMoffs16Effect p 10 moffs) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 10 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_rax_moffs_step s h [0x66] (by simpa using scanPrefix_66) (by simp)
    16 (.inr (.inr rfl)) (by exact rfl)
    (by exact MoffsContext.toSeg ⟨rfl, rfl, rfl, rfl⟩)
    (by rfl)
    (by rfl) moffs hcode.bytesAt hlow (by exact hread)
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) [0x66]) moffs = moffs from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movSpec]

theorem mov_ax_moffs16_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (LoadPre p (fun _ => moffs) 2)
      (codeRange p (0x66 :: 0xA1 :: immBytes 64 moffs))
      (Effect.post (movAxMoffs16Effect p 10 moffs)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movAxMoffs16Effect_components]; simp [Component.Covers]) _)
    (mov_ax_moffs16_effect_step p moffs)

theorem mov_ax_moffs16_triple [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (LoadPre p (fun _ => moffs) 2)
      (codeRange p (encodeMovAxMoffs16 moffs))
      (Effect.post (movAxMoffs16Effect p 10 moffs)) :=
  mov_ax_moffs16_triple_of_bytes p moffs

theorem mov_al_moffs8_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    StepEffect (LoadPre p (fun _ => moffs) 1)
      (codeRange p (0xA0 :: immBytes 64 moffs))
      (movAlMoffs8Effect p 9 moffs) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 9 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hstep := mov_al_moffs8_step s h [] (by simp) (by simp)
    (by exact MoffsContext.toSeg ⟨rfl, rfl, rfl, rfl⟩)
    (by rfl)
    (by rfl) moffs hcode.bytesAt hlow (by exact hread)
  rw [show segAddr (scanContext s.DS (PrefixSegments.ofState s) []) moffs = moffs from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movSpec]

theorem mov_al_moffs8_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (LoadPre p (fun _ => moffs) 1)
      (codeRange p (0xA0 :: immBytes 64 moffs))
      (Effect.post (movAlMoffs8Effect p 9 moffs)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movAlMoffs8Effect_components]; simp [Component.Covers]) _)
    (mov_al_moffs8_effect_step p moffs)

theorem mov_al_moffs8_triple [Bindings] (p : BitVec 64) (moffs : BitVec 64) :
    Triple (LoadPre p (fun _ => moffs) 1)
      (codeRange p (encodeMovAlMoffs8 moffs))
      (Effect.post (movAlMoffs8Effect p 9 moffs)) :=
  mov_al_moffs8_triple_of_bytes p moffs

theorem mov_rax_moffs64_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 64) :
    StepEffect (SegLoadPre p r base (fun _ => moffs) 8)
      (codeRange p (r.prefixByte :: rex :: 0xA1 :: immBytes 64 moffs))
      (movRaxMoffs64SegEffect p 11 base moffs) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 11 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
      withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [rex]
      (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil), scanContext_rex _ _ hr]
  have hstep := mov_rax_moffs_step s h [r.prefixByte, rex] (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
    64 (.inl rfl) (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; exact MoffsContext.withSeg ⟨rfl, rfl, rfl, rfl⟩ hseg)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movSpec]

theorem mov_rax_moffs64_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 64) :
    Triple (SegLoadPre p r base (fun _ => moffs) 8)
      (codeRange p (r.prefixByte :: rex :: 0xA1 :: immBytes 64 moffs))
      (Effect.post (movRaxMoffs64SegEffect p 11 base moffs)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movRaxMoffs64SegEffect_components]; simp [Component.Covers]) _)
    (mov_rax_moffs64_seg_effect_step p r base rex hrex moffs)

theorem mov_rax_moffs64_seg_triple [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegLoadPre p r base (fun _ => moffs) 8)
      (codeRange p (r.prefixByte :: encodeMovRaxMoffs64 moffs))
      (Effect.post (movRaxMoffs64SegEffect p 11 base moffs)) :=
  mov_rax_moffs64_seg_triple_of_bytes p r base 0x48 (by unfold RexWPrefix; decide) moffs

theorem mov_eax_moffs32_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    StepEffect (SegLoadPre p r base (fun _ => moffs) 4)
      (codeRange p (r.prefixByte :: 0xA1 :: immBytes 64 moffs))
      (movEaxMoffs32SegEffect p 10 base moffs) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 10 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := mov_rax_moffs_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    32 (.inr (.inl rfl)) (by rw [hsc]; exact rfl)
    (by rw [hsc]; exact MoffsContext.withSeg ⟨rfl, rfl, rfl, rfl⟩ hseg)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec]

theorem mov_eax_moffs32_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegLoadPre p r base (fun _ => moffs) 4)
      (codeRange p (r.prefixByte :: 0xA1 :: immBytes 64 moffs))
      (Effect.post (movEaxMoffs32SegEffect p 10 base moffs)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movEaxMoffs32SegEffect_components]; simp [Component.Covers]) _)
    (mov_eax_moffs32_seg_effect_step p r base moffs)

theorem mov_eax_moffs32_seg_triple [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegLoadPre p r base (fun _ => moffs) 4)
      (codeRange p (r.prefixByte :: encodeMovEaxMoffs32 moffs))
      (Effect.post (movEaxMoffs32SegEffect p 10 base moffs)) :=
  mov_eax_moffs32_seg_triple_of_bytes p r base moffs

theorem mov_ax_moffs16_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    StepEffect (SegLoadPre p r base (fun _ => moffs) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xA1 :: immBytes 64 moffs))
      (movAxMoffs16SegEffect p 11 base moffs) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 11 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, 0x66] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) [0x66]) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r [0x66]
      (noSegPrefix_cons noSegPrefix_66 noSegPrefix_nil)]
  have hstep := mov_rax_moffs_step s h [r.prefixByte, 0x66] (scanPrefix_seg_cons r (by simpa using scanPrefix_66)) (by simp)
    16 (.inr (.inr rfl)) (by rw [hsc]; exact rfl)
    (by rw [hsc]; exact MoffsContext.withSeg ⟨rfl, rfl, rfl, rfl⟩ hseg)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movSpec]

theorem mov_ax_moffs16_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegLoadPre p r base (fun _ => moffs) 2)
      (codeRange p (r.prefixByte :: 0x66 :: 0xA1 :: immBytes 64 moffs))
      (Effect.post (movAxMoffs16SegEffect p 11 base moffs)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movAxMoffs16SegEffect_components]; simp [Component.Covers]) _)
    (mov_ax_moffs16_seg_effect_step p r base moffs)

theorem mov_ax_moffs16_seg_triple [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegLoadPre p r base (fun _ => moffs) 2)
      (codeRange p (r.prefixByte :: encodeMovAxMoffs16 moffs))
      (Effect.post (movAxMoffs16SegEffect p 11 base moffs)) :=
  mov_ax_moffs16_seg_triple_of_bytes p r base moffs

theorem mov_al_moffs8_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    StepEffect (SegLoadPre p r base (fun _ => moffs) 1)
      (codeRange p (r.prefixByte :: 0xA0 :: immBytes 64 moffs))
      (movAlMoffs8SegEffect p 10 base moffs) := by
  rintro s h hcode ⟨hp, ⟨hseg, hbase⟩, hread⟩
  subst hp hbase
  have hlow : s.RIP.toNat + 10 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
      withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
    rw [scanContext_seg_cons _ _ r []
      noSegPrefix_nil]
  have hstep := mov_al_moffs8_step s h [r.prefixByte] (scanPrefix_seg_cons r (by simp)) (by simp)
    (by rw [hsc]; exact MoffsContext.withSeg ⟨rfl, rfl, rfl, rfl⟩ hseg)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hread)
  simp only [hsc, segAddr_withSeg] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movSpec]

theorem mov_al_moffs8_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegLoadPre p r base (fun _ => moffs) 1)
      (codeRange p (r.prefixByte :: 0xA0 :: immBytes 64 moffs))
      (Effect.post (movAlMoffs8SegEffect p 10 base moffs)) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movAlMoffs8SegEffect_components]; simp [Component.Covers]) _)
    (mov_al_moffs8_seg_effect_step p r base moffs)

theorem mov_al_moffs8_seg_triple [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (moffs : BitVec 64) :
    Triple (SegLoadPre p r base (fun _ => moffs) 1)
      (codeRange p (r.prefixByte :: encodeMovAlMoffs8 moffs))
      (Effect.post (movAlMoffs8SegEffect p 10 base moffs)) :=
  mov_al_moffs8_seg_triple_of_bytes p r base moffs

theorem mov_rax_moffs64_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 32) :
    StepEffect (LoadPre p (fun _ => (moffs.setWidth 64)) 8)
      (codeRange p (0x67 :: rex :: 0xA1 :: immBytes 32 moffs))
      (movRaxMoffs64Effect p 7 (moffs.setWidth 64)) := by
  have hr := hrex.rexPrefix
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 7 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
      withAsz (rexContext s.DS rex.toBitVec) := by
    rw [scanContext_asz_cons, scanContext_rex _ _ hr]
  have hstep := mov_rax_moffs_a32_step s h [0x67, rex] (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
    64 (.inl rfl) (by rw [hsc]; exact hrex.operand_size s.DS)
    (by rw [hsc]; exact MoffsContext.withAsz ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  rw [show segAddr (withAsz (rexContext s.DS rex.toBitVec)) (moffs.setWidth 64) = (moffs.setWidth 64) from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, movSpec]

theorem mov_rax_moffs64_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (moffs : BitVec 32) :
    Triple (LoadPre p (fun _ => (moffs.setWidth 64)) 8)
      (codeRange p (0x67 :: rex :: 0xA1 :: immBytes 32 moffs))
      (Effect.post (movRaxMoffs64Effect p 7 (moffs.setWidth 64))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movRaxMoffs64Effect_components]; simp [Component.Covers]) _)
    (mov_rax_moffs64_a32_effect_step p rex hrex moffs)

theorem mov_rax_moffs64_a32_triple [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (LoadPre p (fun _ => (moffs.setWidth 64)) 8)
      (codeRange p (encodeMovRaxMoffs64A32 moffs))
      (Effect.post (movRaxMoffs64Effect p 7 (moffs.setWidth 64))) :=
  mov_rax_moffs64_a32_triple_of_bytes p 0x48 (by unfold RexWPrefix; decide) moffs

theorem mov_eax_moffs32_a32_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    StepEffect (LoadPre p (fun _ => (moffs.setWidth 64)) 4)
      (codeRange p (0x67 :: 0xA1 :: immBytes 32 moffs))
      (movEaxMoffs32Effect p 6 (moffs.setWidth 64)) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := mov_rax_moffs_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    32 (.inr (.inl rfl)) (by rw [hsc]; exact rfl)
    (by rw [hsc]; exact MoffsContext.withAsz ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])) (moffs.setWidth 64) = (moffs.setWidth 64) from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, movSpec]

theorem mov_eax_moffs32_a32_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (LoadPre p (fun _ => (moffs.setWidth 64)) 4)
      (codeRange p (0x67 :: 0xA1 :: immBytes 32 moffs))
      (Effect.post (movEaxMoffs32Effect p 6 (moffs.setWidth 64))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movEaxMoffs32Effect_components]; simp [Component.Covers]) _)
    (mov_eax_moffs32_a32_effect_step p moffs)

theorem mov_eax_moffs32_a32_triple [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (LoadPre p (fun _ => (moffs.setWidth 64)) 4)
      (codeRange p (encodeMovEaxMoffs32A32 moffs))
      (Effect.post (movEaxMoffs32Effect p 6 (moffs.setWidth 64))) :=
  mov_eax_moffs32_a32_triple_of_bytes p moffs

theorem mov_ax_moffs16_a32_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    StepEffect (LoadPre p (fun _ => (moffs.setWidth 64)) 2)
      (codeRange p (0x67 :: 0x66 :: 0xA1 :: immBytes 32 moffs))
      (movAxMoffs16Effect p 7 (moffs.setWidth 64)) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 7 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, 0x66] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66]) := by
    rw [scanContext_asz_cons]
  have hstep := mov_rax_moffs_a32_step s h [0x67, 0x66] (scanPrefix_asz_cons (by simpa using scanPrefix_66)) (by simp)
    16 (.inr (.inr rfl)) (by rw [hsc]; exact rfl)
    (by rw [hsc]; exact MoffsContext.withAsz ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [0x66])) (moffs.setWidth 64) = (moffs.setWidth 64) from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movSpec]

theorem mov_ax_moffs16_a32_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (LoadPre p (fun _ => (moffs.setWidth 64)) 2)
      (codeRange p (0x67 :: 0x66 :: 0xA1 :: immBytes 32 moffs))
      (Effect.post (movAxMoffs16Effect p 7 (moffs.setWidth 64))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movAxMoffs16Effect_components]; simp [Component.Covers]) _)
    (mov_ax_moffs16_a32_effect_step p moffs)

theorem mov_ax_moffs16_a32_triple [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (LoadPre p (fun _ => (moffs.setWidth 64)) 2)
      (codeRange p (encodeMovAxMoffs16A32 moffs))
      (Effect.post (movAxMoffs16Effect p 7 (moffs.setWidth 64))) :=
  mov_ax_moffs16_a32_triple_of_bytes p moffs

theorem mov_al_moffs8_a32_effect_step [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    StepEffect (LoadPre p (fun _ => (moffs.setWidth 64)) 1)
      (codeRange p (0x67 :: 0xA0 :: immBytes 32 moffs))
      (movAlMoffs8Effect p 6 (moffs.setWidth 64)) := by
  rintro s h hcode ⟨hp, hread⟩
  subst hp
  have hlow : s.RIP.toNat + 6 ≤ 2^32 := by
    have := hcode.low (by simp) (by simp)
    simp only [List.length_cons, immBytes_length] at this
    omega
  have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
      withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
    rw [scanContext_asz_cons]
  have hstep := mov_al_moffs8_a32_step s h [0x67] (scanPrefix_asz_cons (by simp)) (by simp)
    (by rw [hsc]; exact MoffsContext.withAsz ⟨rfl, rfl, rfl, rfl⟩)
    (by rw [hsc]; rfl)
    (by rw [hsc]; rfl) moffs hcode.bytesAt hlow (by rw [hsc]; exact hread)
  simp only [hsc] at hstep
  rw [show segAddr (withAsz (scanContext s.DS (PrefixSegments.ofState s) [])) (moffs.setWidth 64) = (moffs.setWidth 64) from rfl] at hstep
  refine ⟨_, hstep, ReadyToStep.afterStep_load h _ _ _ _,
    ⟨afterStep_load_rip h _ _ _ _, ?_, trivial, AgreesExcept.afterStep_load s _ _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self_merge, Operand.read_afterFetches,
    Operand.read_beforeFetch, Operand.read_reg_dataAccess, movSpec]

theorem mov_al_moffs8_a32_triple_of_bytes [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (LoadPre p (fun _ => (moffs.setWidth 64)) 1)
      (codeRange p (0x67 :: 0xA0 :: immBytes 32 moffs))
      (Effect.post (movAlMoffs8Effect p 6 (moffs.setWidth 64))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by rw [movAlMoffs8Effect_components]; simp [Component.Covers]) _)
    (mov_al_moffs8_a32_effect_step p moffs)

theorem mov_al_moffs8_a32_triple [Bindings] (p : BitVec 64) (moffs : BitVec 32) :
    Triple (LoadPre p (fun _ => (moffs.setWidth 64)) 1)
      (codeRange p (encodeMovAlMoffs8A32 moffs))
      (Effect.post (movAlMoffs8Effect p 6 (moffs.setWidth 64))) :=
  mov_al_moffs8_a32_triple_of_bytes p moffs

attribute [x86_compose] movRaxMoffs64Effect movRaxMoffs64SegEffect movEaxMoffs32Effect movEaxMoffs32SegEffect movAxMoffs16Effect movAxMoffs16SegEffect movAlMoffs8Effect movAlMoffs8SegEffect

@[x86_local] theorem movRaxMoffs64Effect_local {p : BitVec 64} {len : Nat} {moffs : BitVec 64} :
    Effect.Local (movRaxMoffs64Effect p len moffs) := by
  effect_local [movRaxMoffs64Effect]

@[x86_local] theorem movRaxMoffs64SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {moffs : BitVec 64} :
    Effect.Local (movRaxMoffs64SegEffect p len base moffs) := by
  effect_local [movRaxMoffs64SegEffect]

@[x86_local] theorem movEaxMoffs32Effect_local {p : BitVec 64} {len : Nat} {moffs : BitVec 64} :
    Effect.Local (movEaxMoffs32Effect p len moffs) := by
  effect_local [movEaxMoffs32Effect]

@[x86_local] theorem movEaxMoffs32SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {moffs : BitVec 64} :
    Effect.Local (movEaxMoffs32SegEffect p len base moffs) := by
  effect_local [movEaxMoffs32SegEffect]

@[x86_local] theorem movAxMoffs16Effect_local {p : BitVec 64} {len : Nat} {moffs : BitVec 64} :
    Effect.Local (movAxMoffs16Effect p len moffs) := by
  effect_local [movAxMoffs16Effect]

@[x86_local] theorem movAxMoffs16SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {moffs : BitVec 64} :
    Effect.Local (movAxMoffs16SegEffect p len base moffs) := by
  effect_local [movAxMoffs16SegEffect]

@[x86_local] theorem movAlMoffs8Effect_local {p : BitVec 64} {len : Nat} {moffs : BitVec 64} :
    Effect.Local (movAlMoffs8Effect p len moffs) := by
  effect_local [movAlMoffs8Effect]

@[x86_local] theorem movAlMoffs8SegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64} {moffs : BitVec 64} :
    Effect.Local (movAlMoffs8SegEffect p len base moffs) := by
  effect_local [movAlMoffs8SegEffect]

end X86Proofs
