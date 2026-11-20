import X86Proofs.Instructions.MovSreg.Generated.MS.Step
import X86Proofs.Instructions.MovSreg.Generated.MS.Encode
import X86Proofs.Program.Compose

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def movM16SregEffect (p : BitVec 64) (len : Nat) (am : AddrMode)
    (sel : BitVec 16) : RamState → Effect :=
  storeEffect p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) fun _ => movsregSpec 16 sel

@[simp] theorem movM16SregEffect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (sel : BitVec 16) (s : RamState) :
    (movM16SregEffect p len am sel s).components = [.mem (am.addr s (p + BitVec.ofNat 64 len)) (16 / 8), .rip] := rfl

def movM16SregSegEffect (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (sel : BitVec 16) : RamState → Effect :=
  storeEffect p len (fun s => base + am.addr s (p + BitVec.ofNat 64 len)) fun _ => movsregSpec 16 sel

@[simp] theorem movM16SregSegEffect_components (p : BitVec 64) (len : Nat) (base : BitVec 64) (am : AddrMode)
    (sel : BitVec 16) (s : RamState) :
    (movM16SregSegEffect p len base am sel s).components = [.mem (base + am.addr s (p + BitVec.ofNat 64 len)) (16 / 8), .rip] := rfl

def movM16SregA32Effect (p : BitVec 64) (len : Nat) (am : AddrMode)
    (sel : BitVec 16) : RamState → Effect :=
  storeEffect p len (fun s => am.addr32 s (p + BitVec.ofNat 64 len)) fun _ => movsregSpec 16 sel

@[simp] theorem movM16SregA32Effect_components (p : BitVec 64) (len : Nat) (am : AddrMode)
    (sel : BitVec 16) (s : RamState) :
    (movM16SregA32Effect p len am sel s).components = [.mem (am.addr32 s (p + BitVec.ofNat 64 len)) (16 / 8), .rip] := rfl

theorem mov_m16_sreg_effect_step [Bindings] (p : BitVec 64) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (sel : BitVec 16) :
    StepEffect (fun s => StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (0x8C :: am.modrm sreg :: am.tail))
      (movM16SregEffect p (2 + am.tail.length) am sel) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hsel⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (2 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m16_sreg_step s h []
        (by simp) (by simp)
        (by rfl) (by rfl) (by rfl) sreg hsreg am hv
        (by exact (AddrContext.legacy _ am hx hb).toSeg)
        hcode.bytesAt hlow (by exact hw)
      simp only [List.length_nil, Nat.zero_add] at hstep
      rw [hsel] at hstep
      exact hstep

theorem mov_m16_sreg_triple_of_bytes [Bindings] (p : BitVec 64) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (sel : BitVec 16) :
    Triple (fun s => StorePre p (2 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (2 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (0x8C :: am.modrm sreg :: am.tail))
      (Effect.post (movM16SregEffect p (2 + am.tail.length) am sel)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1)
    (mov_m16_sreg_effect_step p sreg hsreg am hv hx hb sel)

theorem mov_m16_sreg_rex_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (sel : BitVec 16) :
    StepEffect (fun s => StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (rex :: 0x8C :: am.modrm sreg :: am.tail))
      (movM16SregEffect p (3 + am.tail.length) am sel) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨⟨hp, hw, _⟩, hsel⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hstep := mov_m16_sreg_step s h [rex]
        (by simpa using hr.scanPrefix) (by simp)
        (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) (by rw [scanContext_rex _ _ hr]; rfl) sreg hsreg am hv
        (by rw [scanContext_rex _ _ hr]; exact (AddrContext.rex _ _ am hx hb).toSeg)
        hcode.bytesAt hlow (by rw [scanContext_rex _ _ hr]; exact hw)
      simp only [scanContext_rex _ _ hr] at hstep
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem mov_m16_sreg_rex_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (sel : BitVec 16) :
    Triple (fun s => StorePre p (3 + am.tail.length)
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (rex :: 0x8C :: am.modrm sreg :: am.tail))
      (Effect.post (movM16SregEffect p (3 + am.tail.length) am sel)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1)
    (mov_m16_sreg_rex_effect_step p rex hrex sreg hsreg am hv hx hb sel)

theorem mov_m16_sreg_triple [Bindings] (p : BitVec 64)
    (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode) (hv : am.Valid) (sel : BitVec 16) :
    Triple (fun s => StorePre p (encodeMovM16Sreg sreg am).length
        (fun s => am.addr s (p + BitVec.ofNat 64 (encodeMovM16Sreg sreg am).length)) 2 s ∧
        segSelector s sreg = sel)
      (codeRange p (encodeMovM16Sreg sreg am))
      (Effect.post (movM16SregEffect p (encodeMovM16Sreg sreg am).length am sel)) := by
  unfold encodeMovM16Sreg
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := mov_m16_sreg_triple_of_bytes p sreg hsreg am hv hx hb sel
    rwa [show (0x8C :: am.modrm sreg :: am.tail).length = 2 + am.tail.length by
      simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := mov_m16_sreg_rex_triple_of_bytes p _ hrex sreg hsreg am hv hx hb sel
    rwa [show (am.rexByte false 0 :: 0x8C :: am.modrm sreg :: am.tail).length =
      3 + am.tail.length by simp; omega]

theorem mov_m16_sreg_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (sel : BitVec 16) :
    StepEffect (fun s => SegStorePre p (3 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (r.prefixByte :: 0x8C :: am.modrm sreg :: am.tail))
      (movM16SregSegEffect p (3 + am.tail.length) base am sel) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1.store)
    fun s h hcode hpre => by
      obtain ⟨⟨⟨hp, hw, _⟩, hseg, hbase⟩, hsel⟩ := hpre
      subst hp hbase
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte] =
          withSeg (scanContext s.DS (PrefixSegments.ofState s) []) (r.select (PrefixSegments.ofState s)) := by
        rw [scanContext_seg_cons _ _ r []
          noSegPrefix_nil]
      have hstep := mov_m16_sreg_step s h [r.prefixByte]
        (scanPrefix_seg_cons r (by simp)) (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) sreg hsreg am hv
        (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).withSeg hseg)
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem mov_m16_sreg_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (sel : BitVec 16) :
    Triple (fun s => SegStorePre p (3 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (r.prefixByte :: 0x8C :: am.modrm sreg :: am.tail))
      (Effect.post (movM16SregSegEffect p (3 + am.tail.length) base am sel)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (mov_m16_sreg_seg_effect_step p r base sreg hsreg am hv hx hb sel)

theorem mov_m16_sreg_rex_seg_effect_step [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (sel : BitVec 16) :
    StepEffect (fun s => SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (r.prefixByte :: rex :: 0x8C :: am.modrm sreg :: am.tail))
      (movM16SregSegEffect p (4 + am.tail.length) base am sel) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1.store)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨⟨⟨hp, hw, _⟩, hseg, hbase⟩, hsel⟩ := hpre
      subst hp hbase
      have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [r.prefixByte, rex] =
          withSeg (rexContext s.DS rex.toBitVec) (r.select (PrefixSegments.ofState s)) := by
        rw [scanContext_seg_cons _ _ r [rex]
          (noSegPrefix_cons hr.noSegPrefix noSegPrefix_nil),
          scanContext_rex _ _ hr]
      have hstep := mov_m16_sreg_step s h [r.prefixByte, rex]
        (scanPrefix_seg_cons r (by simpa using hr.scanPrefix)) (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) sreg hsreg am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).withSeg hseg)
        hcode.bytesAt hlow (by rw [hsc, segAddr_withSeg]; exact hw)
      simp only [hsc, segAddr_withSeg, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem mov_m16_sreg_rex_seg_triple_of_bytes [Bindings] (p : BitVec 64) (r : SegReg)
    (base : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (sel : BitVec 16) :
    Triple (fun s => SegStorePre p (4 + am.tail.length) r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (r.prefixByte :: rex :: 0x8C :: am.modrm sreg :: am.tail))
      (Effect.post (movM16SregSegEffect p (4 + am.tail.length) base am sel)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1.store)
    (mov_m16_sreg_rex_seg_effect_step p r base rex hrex sreg hsreg am hv hx hb sel)

theorem mov_m16_sreg_seg_triple [Bindings] (p : BitVec 64) (r : SegReg) (base : BitVec 64)
    (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode) (hv : am.Valid) (sel : BitVec 16) :
    Triple (fun s => SegStorePre p (r.prefixByte :: encodeMovM16Sreg sreg am).length r base
        (fun s => am.addr s (p + BitVec.ofNat 64 (r.prefixByte :: encodeMovM16Sreg sreg am).length)) 2 s ∧
        segSelector s sreg = sel)
      (codeRange p (r.prefixByte :: encodeMovM16Sreg sreg am))
      (Effect.post (movM16SregSegEffect p (r.prefixByte :: encodeMovM16Sreg sreg am).length base am sel)) := by
  unfold encodeMovM16Sreg
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := mov_m16_sreg_seg_triple_of_bytes p r base sreg hsreg am hv hx hb sel
    rwa [show (r.prefixByte :: 0x8C :: am.modrm sreg :: am.tail).length = 3 + am.tail.length by
      simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := mov_m16_sreg_rex_seg_triple_of_bytes p r base _ hrex sreg hsreg am hv hx hb sel
    rwa [show (r.prefixByte :: am.rexByte false 0 :: 0x8C :: am.modrm sreg :: am.tail).length =
      4 + am.tail.length by simp; omega]

theorem mov_m16_sreg_a32_effect_step [Bindings] (p : BitVec 64) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (sel : BitVec 16) :
    StepEffect (fun s => StorePre p (3 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (0x67 :: 0x8C :: am.modrm sreg :: am.tail))
      (movM16SregA32Effect p (3 + am.tail.length) am sel) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode hpre => by
      obtain ⟨⟨hp, hw, _⟩, hsel⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (3 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67] =
          withAsz (scanContext s.DS (PrefixSegments.ofState s) []) := by
        rw [scanContext_asz_cons]
      have hstep := mov_m16_sreg_a32_step s h [0x67]
        (scanPrefix_asz_cons (by simp)) (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) sreg hsreg am hv
        (by rw [hsc]; exact (AddrContext.legacy _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem mov_m16_sreg_a32_triple_of_bytes [Bindings] (p : BitVec 64) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : am.rexX = 0) (hb : am.rexB = 0) (sel : BitVec 16) :
    Triple (fun s => StorePre p (3 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (3 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (0x67 :: 0x8C :: am.modrm sreg :: am.tail))
      (Effect.post (movM16SregA32Effect p (3 + am.tail.length) am sel)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1)
    (mov_m16_sreg_a32_effect_step p sreg hsreg am hv hx hb sel)

theorem mov_m16_sreg_rex_a32_effect_step [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (sel : BitVec 16) :
    StepEffect (fun s => StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (0x67 :: rex :: 0x8C :: am.modrm sreg :: am.tail))
      (movM16SregA32Effect p (4 + am.tail.length) am sel) :=
  StepEffect.of_store_pre (n := 16) (by decide) (by decide) _ _ (fun _ hs => hs.1)
    fun s h hcode hpre => by
      have hr := hrex.rexPrefix
      obtain ⟨⟨hp, hw, _⟩, hsel⟩ := hpre
      subst hp
      have hlow : s.RIP.toNat + (4 + am.tail.length) ≤ 2^32 := by
        have := am.tail_length_le
        have := hcode.low (by simp) (by simp; omega)
        simp only [List.length_cons] at this
        omega
      have hsc : scanContext s.DS (PrefixSegments.ofState s) [0x67, rex] =
          withAsz (rexContext s.DS rex.toBitVec) := by
        rw [scanContext_asz_cons, scanContext_rex _ _ hr]
      have hstep := mov_m16_sreg_a32_step s h [0x67, rex]
        (scanPrefix_asz_cons (by simpa using hr.scanPrefix)) (by simp)
        (by rw [hsc]; rfl) (by rw [hsc]; rfl) (by rw [hsc]; rfl) sreg hsreg am hv
        (by rw [hsc]; exact (AddrContext.rex _ _ am hx hb).toSeg.withAsz)
        hcode.bytesAt hlow (by rw [hsc]; exact hw)
      simp only [hsc] at hstep
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] at hstep
      rw [hsel] at hstep
      exact hstep

theorem mov_m16_sreg_rex_a32_triple_of_bytes [Bindings] (p : BitVec 64) (rex : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode)
    (hv : am.Valid) (hx : rexX rex.toBitVec = am.rexX) (hb : rexB rex.toBitVec = am.rexB)
    (sel : BitVec 16) :
    Triple (fun s => StorePre p (4 + am.tail.length)
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (4 + am.tail.length))) 2 s ∧ segSelector s sreg = sel)
      (codeRange p (0x67 :: rex :: 0x8C :: am.modrm sreg :: am.tail))
      (Effect.post (movM16SregA32Effect p (4 + am.tail.length) am sel)) :=
  Triple.of_effect (fun _ hpre => storeEffect_avoids (by simp; omega) _ _ hpre.1)
    (mov_m16_sreg_rex_a32_effect_step p rex hrex sreg hsreg am hv hx hb sel)

theorem mov_m16_sreg_a32_triple [Bindings] (p : BitVec 64)
    (sreg : BitVec 3) (hsreg : sreg.toNat < 6) (am : AddrMode) (hv : am.Valid) (sel : BitVec 16) :
    Triple (fun s => StorePre p (0x67 :: encodeMovM16Sreg sreg am).length
        (fun s => am.addr32 s (p + BitVec.ofNat 64 (0x67 :: encodeMovM16Sreg sreg am).length)) 2 s ∧
        segSelector s sreg = sel)
      (codeRange p (0x67 :: encodeMovM16Sreg sreg am))
      (Effect.post (movM16SregA32Effect p (0x67 :: encodeMovM16Sreg sreg am).length am sel)) := by
  unfold encodeMovM16Sreg
  split
  · rename_i hc
    obtain ⟨hx, hb⟩ := hc
    have := mov_m16_sreg_a32_triple_of_bytes p sreg hsreg am hv hx hb sel
    rwa [show (0x67 :: 0x8C :: am.modrm sreg :: am.tail).length = 3 + am.tail.length by
      simp; omega]
  · obtain ⟨hrex, -, hx, hb⟩ := am.rexByte_false_spec 0
    have := mov_m16_sreg_rex_a32_triple_of_bytes p _ hrex sreg hsreg am hv hx hb sel
    rwa [show (0x67 :: am.rexByte false 0 :: 0x8C :: am.modrm sreg :: am.tail).length =
      4 + am.tail.length by simp; omega]

attribute [x86_compose] movM16SregEffect movM16SregSegEffect movM16SregA32Effect

@[x86_local] theorem movM16SregEffect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {sel : BitVec 16} :
    Effect.Local (movM16SregEffect p len am sel) := by
  effect_local [movM16SregEffect, storeEffect]

@[x86_local] theorem movM16SregSegEffect_local {p : BitVec 64} {len : Nat} {base : BitVec 64}
    {am : AddrMode} {sel : BitVec 16} :
    Effect.Local (movM16SregSegEffect p len base am sel) := by
  effect_local [movM16SregSegEffect, storeEffect]

@[x86_local] theorem movM16SregA32Effect_local {p : BitVec 64} {len : Nat} {am : AddrMode}
    {sel : BitVec 16} :
    Effect.Local (movM16SregA32Effect p len am sel) := by
  effect_local [movM16SregA32Effect, storeEffect]

end X86Proofs
