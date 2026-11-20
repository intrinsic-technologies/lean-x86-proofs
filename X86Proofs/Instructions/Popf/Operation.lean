import X86Proofs.Program.ReadWrite.Rflags

/-!
# POPF/POPFQ specification

`POPFQ` (`9D`) pops 8 bytes into RFLAGS, `POPF` (`66 9D`) 2 bytes into FLAGS (bits 0–15). Intel
SDM, 64-bit mode with CPL > 0: if CPL > IOPL, "all non-reserved bits except IF, IOPL, VIP, VIF,
VM and RF can be modified; IF, IOPL, VIP, VIF, VM and all reserved bits are unaffected"; with the
16-bit operand size only bits 0–15 are popped (AC and ID are kept). lean-x86 writes IF only if
CPL ≤ IOPL and IOPL only if CPL = 0, and ignores the popped RF (the step clears RF before the
instruction runs), so with CPL > IOPL the bits written are CF, PF, AF, ZF, SF, TF, DF, OF, NT
(`popf16Mask`) and at 64 bits AC and ID too (`popfMask`): `popfSpec v r`, `popf16Spec v r`.
-/

namespace X86Proofs

/-- The RFLAGS bits POPFQ writes with CPL > IOPL: CF (0), PF (2), AF (4), ZF (6), SF (7), TF (8),
DF (10), OF (11), NT (14), AC (18), ID (21). -/
def popfMask : BitVec 64 := 0x244DD5#64

/-- The FLAGS bits POPF (16-bit) writes with CPL > IOPL: CF, PF, AF, ZF, SF, TF, DF, OF, NT. -/
def popf16Mask : BitVec 64 := 0x4DD5#64

/-- RFLAGS after POPFQ pops `v` with CPL > IOPL, from RFLAGS `r`: the `popfMask` bits of `v`, the
other bits of `r`. -/
def popfSpec (v r : BitVec 64) : BitVec 64 := (v &&& popfMask) ||| (r &&& ~~~popfMask)

/-- RFLAGS after POPF (16-bit) pops `v` with CPL > IOPL, from RFLAGS `r`: the `popf16Mask` bits of
`v`, the other bits of `r`. -/
def popf16Spec (v : BitVec 16) (r : BitVec 64) : BitVec 64 :=
  (v.setWidth 64 &&& popf16Mask) ||| (r &&& ~~~popf16Mask)

/-- POPFQ keeps the RFLAGS bits it may write but no effect states: the popped `v` has the TF
(8), NT (14), AC (18) and ID (21) bits of RFLAGS `r` (TF clear in every state ready to step: a
popped TF = 1 would request a single-step trap). -/
structure PopfKeeps (v r : BitVec 64) : Prop where
  tf : v.getLsbD 8 = r.getLsbD 8
  nt : v.getLsbD 14 = r.getLsbD 14
  ac : v.getLsbD 18 = r.getLsbD 18
  id : v.getLsbD 21 = r.getLsbD 21

/-- POPF (16-bit) keeps TF (8) and NT (14): the popped `v` has those bits of RFLAGS `r`. -/
structure Popf16Keeps (v : BitVec 16) (r : BitVec 64) : Prop where
  tf : v.getLsbD 8 = r.getLsbD 8
  nt : v.getLsbD 14 = r.getLsbD 14

open X86 X86.Machine

/-- The state after POPFQ from `t` (CPL > IOPL): RFLAGS `popfSpec` of the 8 bytes at RSP, RSP
advanced by 8, the bookkeeping of the load. -/
def popfqState (t : RamState) : RamState :=
  (Operand.reg 4 : Operand 64).write
    { dataAccess t "load" with
      RFLAGS := popfSpec ((Operand.mem (stackPtr t) : Operand 64).read t) t.RFLAGS }
    (stackPtr t + 8)

/-- The state after POPF (16-bit) from `t` (CPL > IOPL): RFLAGS `popf16Spec` of the 2 bytes at
RSP, RSP advanced by 2. -/
def popfState (t : RamState) : RamState :=
  (Operand.reg 4 : Operand 64).write
    { dataAccess t "load" with
      RFLAGS := popf16Spec ((Operand.mem (stackPtr t) : Operand 16).read t) t.RFLAGS }
    (stackPtr t + 2)

/-- What POPFQ at `p` needs besides `ReadyToStep`: RIP = `p`, the 8 bytes at RSP readable,
CPL > IOPL (so IF and IOPL are not written), and the popped value keeps TF, NT, AC and ID. -/
structure PopfqPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  read : MemReadable s (stackPtr s) 8
  iopl : X86.Runtime.Unsigned (s.RFLAGS.extractLsb' 12 2) < s.CPL
  keeps : PopfKeeps ((Operand.mem (stackPtr s) : Operand 64).read s) s.RFLAGS

/-- What POPF (16-bit) at `p` needs besides `ReadyToStep`: RIP = `p`, the 2 bytes at RSP
readable, CPL > IOPL, and the popped value keeps TF and NT. -/
structure PopfPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  read : MemReadable s (stackPtr s) 2
  iopl : X86.Runtime.Unsigned (s.RFLAGS.extractLsb' 12 2) < s.CPL
  keeps : Popf16Keeps ((Operand.mem (stackPtr s) : Operand 16).read s) s.RFLAGS

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem popfChain_eq (v r : BitVec 64) :
    RFLAGS_Type.setID (RFLAGS_Type.setAC (RFLAGS_Type.setNT (RFLAGS_Type.setOF
      (RFLAGS_Type.setDF (RFLAGS_Type.setTF (RFLAGS_Type.setSF (RFLAGS_Type.setZF
        (RFLAGS_Type.setAF (RFLAGS_Type.setPF (RFLAGS_Type.setCF r
          (v.extractLsb' (Int.toNat 0) (Int.toNat 1))) (v.extractLsb' (Int.toNat 2) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 4) (Int.toNat 1))) (v.extractLsb' (Int.toNat 6) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 7) (Int.toNat 1))) (v.extractLsb' (Int.toNat 8) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 10) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 11) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 14) (Int.toNat 1))) (v.extractLsb' 18 1))
      (v.extractLsb' 21 1) = popfSpec v r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hm : (0x244DD5#64).getLsbD j = decide (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨
      j = 10 ∨ j = 11 ∨ j = 14 ∨ j = 18 ∨ j = 21) :=
    (show ∀ k : Fin 64, (0x244DD5#64).getLsbD k.val = decide (k.val = 0 ∨ k.val = 2 ∨
      k.val = 4 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 10 ∨ k.val = 11 ∨ k.val = 14 ∨
      k.val = 18 ∨ k.val = 21) by decide) ⟨j, hj⟩
  simp only [RFLAGS_Type.setCF, RFLAGS_Type.setPF, RFLAGS_Type.setAF, RFLAGS_Type.setZF,
    RFLAGS_Type.setSF, RFLAGS_Type.setTF, RFLAGS_Type.setDF, RFLAGS_Type.setOF, RFLAGS_Type.setNT,
    RFLAGS_Type.setAC, RFLAGS_Type.setID, popfSpec, popfMask, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, getLsbD_setSlice _ _ _ _ _ hj, hm,
    show ∀ k, (k ≤ j ∧ j < k + 1) ↔ j = k from fun k => by omega]
  by_cases h : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 10 ∨ j = 11 ∨ j = 14 ∨
      j = 18 ∨ j = 21
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [not_or] at h
    simp [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2,
      show j < 64 from hj]

theorem popfq_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 8)
    (hiopl : X86.Runtime.Unsigned (t.RFLAGS.extractLsb' 12 2) < t.CPL) :
    (X86.Instructions.Operations.POP_FLAGS 64).run t =
      (.ok (), popfqState t) := by
  have hmode := in64BitMode_of_userCodeSegment h.cs h.efer.lma
  unfold X86.Instructions.Operations.POP_FLAGS
  spec_run [MonadState.get => get_run _, In_64Bit_Mode => hmode, RSP => rsp_run _,
    Pop_Stack => popStack_run t h hss (stackPtr t) hr]
  have hcpl : 0 < t.CPL := by
    have := hiopl
    rw [unsigned_eq] at this
    omega
  have hc1 : decide ((dataAccess t "load").CPL ≤ X86.Runtime.Unsigned
      (BitVec.extractLsb' (Int.toNat 12) (Int.toNat 2) (dataAccess t "load").RFLAGS)) = false :=
    decide_eq_false (Int.not_le.mpr hiopl)
  have hc0 : ((dataAccess t "load").CPL == 0) = false := by
    simp only [dataAccess, beq_eq_false_iff_ne]
    omega
  simp only [hc1, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (get_run _)).trans ?_
  simp only [hc0, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  have hrd (k : Nat) (hk : k < 64) (u : RamState) : (do
      X86.Runtime.assert (decide (k < 64))
      X86.Runtime.CheckedSlice.read ((Operand.mem (stackPtr t) : Operand 64).read t) k 1 :
        X86.Runtime.SpecM X86.Exception RamState (BitVec 1)).run u =
      (.ok (((Operand.mem (stackPtr t) : Operand 64).read t).extractLsb' k 1), u) := by
    simp only [hk, decide_true, assert_of_true, pure_bind]
    rw [checkedSliceRead_eq_pure _ (by omega) (by omega) (by omega)]
    rfl
  refine (specM_bind_run _ _ (hrd 18 (by decide) _)).trans ?_
  refine (specM_bind_run _ _ (hrd 21 (by decide) _)).trans ?_
  refine (specM_bind_run _ _ rfl).trans ?_
  rw [writeRSP64_run, popfChain_eq]
  rfl

theorem popf16Chain_eq (v : BitVec 16) (r : BitVec 64) :
    RFLAGS_Type.setNT (RFLAGS_Type.setOF
      (RFLAGS_Type.setDF (RFLAGS_Type.setTF (RFLAGS_Type.setSF (RFLAGS_Type.setZF
        (RFLAGS_Type.setAF (RFLAGS_Type.setPF (RFLAGS_Type.setCF r
          (v.extractLsb' (Int.toNat 0) (Int.toNat 1))) (v.extractLsb' (Int.toNat 2) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 4) (Int.toNat 1))) (v.extractLsb' (Int.toNat 6) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 7) (Int.toNat 1))) (v.extractLsb' (Int.toNat 8) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 10) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 11) (Int.toNat 1)))
          (v.extractLsb' (Int.toNat 14) (Int.toNat 1)) = popf16Spec v r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hm : (0x4DD5#64).getLsbD j = decide (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨
      j = 10 ∨ j = 11 ∨ j = 14) :=
    (show ∀ k : Fin 64, (0x4DD5#64).getLsbD k.val = decide (k.val = 0 ∨ k.val = 2 ∨
      k.val = 4 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 10 ∨ k.val = 11 ∨ k.val = 14) by
      decide) ⟨j, hj⟩
  simp only [RFLAGS_Type.setCF, RFLAGS_Type.setPF, RFLAGS_Type.setAF, RFLAGS_Type.setZF,
    RFLAGS_Type.setSF, RFLAGS_Type.setTF, RFLAGS_Type.setDF, RFLAGS_Type.setOF, RFLAGS_Type.setNT,
    popf16Spec, popf16Mask, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    getLsbD_setSlice _ _ _ _ _ hj, hm, show ∀ k, (k ≤ j ∧ j < k + 1) ↔ j = k from fun k => by omega]
  by_cases h : j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 10 ∨ j = 11 ∨ j = 14
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [not_or] at h
    simp [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, show j < 64 from hj]

theorem popf_operation [Bindings] (t : RamState) (h : DataReady t)
    (hss : t.SS = userStackSegment) (hr : MemReadable t (stackPtr t) 2)
    (hiopl : X86.Runtime.Unsigned (t.RFLAGS.extractLsb' 12 2) < t.CPL) :
    (X86.Instructions.Operations.POP_FLAGS 16).run t =
      (.ok (), popfState t) := by
  have hmode := in64BitMode_of_userCodeSegment h.cs h.efer.lma
  unfold X86.Instructions.Operations.POP_FLAGS
  spec_run [MonadState.get => get_run _, In_64Bit_Mode => hmode, RSP => rsp_run _,
    Pop_Stack => popStack16_run t h hss (stackPtr t) hr]
  have hcpl : 0 < t.CPL := by
    have := hiopl
    rw [unsigned_eq] at this
    omega
  have hc1 : decide ((dataAccess t "load").CPL ≤ X86.Runtime.Unsigned
      (BitVec.extractLsb' (Int.toNat 12) (Int.toNat 2) (dataAccess t "load").RFLAGS)) = false :=
    decide_eq_false (Int.not_le.mpr hiopl)
  have hc0 : ((dataAccess t "load").CPL == 0) = false := by
    simp only [dataAccess, beq_eq_false_iff_ne]
    omega
  simp only [hc1, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ (get_run _)).trans ?_
  simp only [hc0, Bool.false_eq_true, ↓reduceIte]
  refine (specM_bind_run _ _ rfl).trans ?_
  rw [writeRSP64_run, popf16Chain_eq]
  rfl

theorem bit_popfSpec (v r : BitVec 64) (j : Nat) (hj : j < 64) :
    (popfSpec v r).getLsbD j = if j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 10 ∨
      j = 11 ∨ j = 14 ∨ j = 18 ∨ j = 21 then v.getLsbD j else r.getLsbD j := by
  have hm : (0x244DD5#64).getLsbD j = decide (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨
      j = 10 ∨ j = 11 ∨ j = 14 ∨ j = 18 ∨ j = 21) :=
    (show ∀ k : Fin 64, (0x244DD5#64).getLsbD k.val = decide (k.val = 0 ∨ k.val = 2 ∨
      k.val = 4 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 10 ∨ k.val = 11 ∨ k.val = 14 ∨
      k.val = 18 ∨ k.val = 21) by decide) ⟨j, hj⟩
  simp only [popfSpec, popfMask, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hm]
  split <;> simp_all

theorem bit_popf16Spec (v : BitVec 16) (r : BitVec 64) (j : Nat) (hj : j < 64) :
    (popf16Spec v r).getLsbD j = if j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 10 ∨
      j = 11 ∨ j = 14 then (v.setWidth 64).getLsbD j else r.getLsbD j := by
  have hm : (0x4DD5#64).getLsbD j = decide (j = 0 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨
      j = 10 ∨ j = 11 ∨ j = 14) :=
    (show ∀ k : Fin 64, (0x4DD5#64).getLsbD k.val = decide (k.val = 0 ∨ k.val = 2 ∨
      k.val = 4 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 10 ∨ k.val = 11 ∨ k.val = 14) by
      decide) ⟨j, hj⟩
  simp only [popf16Spec, popf16Mask, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    hm]
  split <;> simp_all

theorem ofRFLAGS_popfSpec (v r : BitVec 64) :
    StatusFlags.ofRFLAGS (popfSpec v r) = StatusFlags.ofRFLAGS v := by
  simp (config := { decide := true }) only [StatusFlags.ofRFLAGS,
    bit_popfSpec v r 0 (by decide),
    bit_popfSpec v r 2 (by decide),
    bit_popfSpec v r 4 (by decide),
    bit_popfSpec v r 6 (by decide),
    bit_popfSpec v r 7 (by decide),
    bit_popfSpec v r 11 (by decide),
    ↓reduceIte]

theorem dfBit_popfSpec (v r : BitVec 64) : dfBit (popfSpec v r) = dfBit v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simpa [dfBit] using bit_popfSpec v r 10 (by decide)

theorem ofRFLAGS_popf16Spec (v : BitVec 16) (r : BitVec 64) :
    StatusFlags.ofRFLAGS (popf16Spec v r) = StatusFlags.ofRFLAGS (v.setWidth 64) := by
  simp (config := { decide := true }) only [StatusFlags.ofRFLAGS,
    bit_popf16Spec v r 0 (by decide),
    bit_popf16Spec v r 2 (by decide),
    bit_popf16Spec v r 4 (by decide),
    bit_popf16Spec v r 6 (by decide),
    bit_popf16Spec v r 7 (by decide),
    bit_popf16Spec v r 11 (by decide),
    ↓reduceIte]

theorem dfBit_popf16Spec (v : BitVec 16) (r : BitVec 64) :
    dfBit (popf16Spec v r) = dfBit (v.setWidth 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have : i = 0 := by omega
  subst this
  simpa [dfBit] using bit_popf16Spec v r 10 (by decide)

theorem fixed_popfSpec {v r : BitVec 64} (hk : PopfKeeps v r) :
    clearDirectionFlag (clearStatusFlags (popfSpec v r)) =
      clearDirectionFlag (clearStatusFlags r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hm : (~~~0x400#64 &&& ~~~0x8D5#64).getLsbD j = decide (j ≠ 0 ∧ j ≠ 2 ∧ j ≠ 4 ∧ j ≠ 6 ∧
      j ≠ 7 ∧ j ≠ 10 ∧ j ≠ 11) :=
    (show ∀ k : Fin 64, (~~~0x400#64 &&& ~~~0x8D5#64).getLsbD k.val = decide (k.val ≠ 0 ∧
      k.val ≠ 2 ∧ k.val ≠ 4 ∧ k.val ≠ 6 ∧ k.val ≠ 7 ∧ k.val ≠ 10 ∧ k.val ≠ 11) by decide) ⟨j, hj⟩
  have he : ∀ x : BitVec 64, (clearDirectionFlag (clearStatusFlags x)).getLsbD j =
      (x.getLsbD j && (~~~0x400#64 &&& ~~~0x8D5#64).getLsbD j) := by
    intro x
    simp only [clearDirectionFlag, clearStatusFlags, BitVec.getLsbD_and, Bool.and_assoc,
      Bool.and_comm ((~~~0x8D5#64).getLsbD j)]
  rw [he, he, hm, bit_popfSpec _ _ _ hj]
  by_cases h8 : j = 8
  · subst h8; simpa using hk.tf
  by_cases h14 : j = 14
  · subst h14; simpa using hk.nt
  by_cases h18 : j = 18
  · subst h18; simpa using hk.ac
  by_cases h21 : j = 21
  · subst h21; simpa using hk.id
  split
  · rename_i hc
    simp only [h8, h14, h18, h21, or_false, false_or] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rfl

theorem fixed_popf16Spec {v : BitVec 16} {r : BitVec 64} (hk : Popf16Keeps v r) :
    clearDirectionFlag (clearStatusFlags (popf16Spec v r)) =
      clearDirectionFlag (clearStatusFlags r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hm : (~~~0x400#64 &&& ~~~0x8D5#64).getLsbD j = decide (j ≠ 0 ∧ j ≠ 2 ∧ j ≠ 4 ∧ j ≠ 6 ∧
      j ≠ 7 ∧ j ≠ 10 ∧ j ≠ 11) :=
    (show ∀ k : Fin 64, (~~~0x400#64 &&& ~~~0x8D5#64).getLsbD k.val = decide (k.val ≠ 0 ∧
      k.val ≠ 2 ∧ k.val ≠ 4 ∧ k.val ≠ 6 ∧ k.val ≠ 7 ∧ k.val ≠ 10 ∧ k.val ≠ 11) by decide) ⟨j, hj⟩
  have he : ∀ x : BitVec 64, (clearDirectionFlag (clearStatusFlags x)).getLsbD j =
      (x.getLsbD j && (~~~0x400#64 &&& ~~~0x8D5#64).getLsbD j) := by
    intro x
    simp only [clearDirectionFlag, clearStatusFlags, BitVec.getLsbD_and, Bool.and_assoc,
      Bool.and_comm ((~~~0x8D5#64).getLsbD j)]
  rw [he, he, hm, bit_popf16Spec _ _ _ hj]
  by_cases h8 : j = 8
  · subst h8; simpa using hk.tf
  by_cases h14 : j = 14
  · subst h14; simpa using hk.nt
  split
  · rename_i hc
    simp only [h8, h14, or_false, false_or] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rfl

theorem AgreesExcept.of_popfqState (t : RamState)
    (hk : PopfKeeps ((Operand.mem (stackPtr t) : Operand 64).read t) t.RFLAGS) :
    AgreesExcept [.df, .reg 4, .flags] t (popfqState t) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      have hne : (4 : BitVec 5) ≠ r := fun h => hc (h ▸ by simp)
      have := Operand.read_write_reg_of_ne (m := 64) { dataAccess t "load" with
        RFLAGS := popfSpec ((Operand.mem (stackPtr t) : Operand 64).read t) t.RFLAGS } hne
        (stackPtr t + 8)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => exact absurd (by simp) hc
    | df => exact absurd (by simp) hc
    | rip => show _ = _; simp only [popfqState, Operand.write, dataAccess]
    | mem a len => exact fun _ _ => rfl
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by simp only [popfqState, Operand.write, dataAccess]) x
    | mxcsr => show _ = _; simp only [popfqState, Operand.write, dataAccess]
    | fpr x =>
      exact Component.agrees_fpr_of_fp87 (by simp only [popfqState, Operand.write, dataAccess]) x
    | fsw => show _ = _; simp only [popfqState, Operand.write, dataAccess]
    | fcc => show _ = _; simp only [popfqState, Operand.write, dataAccess]
    | ftw => show _ = _; simp only [popfqState, Operand.write, dataAccess]
    | fcw => show _ = _; simp only [popfqState, Operand.write, dataAccess]
    | fpuPtr => show _ = _; simp only [popfqState, Operand.write, dataAccess, fpuPtrOf]
  · simp only [fixedPart, popfqState, Operand.write, dataAccess, beforeFetch, resetStepFields,
      fixed_popfSpec hk]

theorem AgreesExcept.of_popfState (t : RamState)
    (hk : Popf16Keeps ((Operand.mem (stackPtr t) : Operand 16).read t) t.RFLAGS) :
    AgreesExcept [.df, .reg 4, .flags] t (popfState t) := by
  refine ⟨fun c hc _ => ?_, fun _ _ => rfl, ?_, fun _ h => h⟩
  · cases c with
    | reg r =>
      have hne : (4 : BitVec 5) ≠ r := fun h => hc (h ▸ by simp)
      have := Operand.read_write_reg_of_ne (m := 64) { dataAccess t "load" with
        RFLAGS := popf16Spec ((Operand.mem (stackPtr t) : Operand 16).read t) t.RFLAGS } hne
        (stackPtr t + 2)
      simp only [Operand.read_reg64] at this
      exact this
    | flags => exact absurd (by simp) hc
    | df => exact absurd (by simp) hc
    | rip => show _ = _; simp only [popfState, Operand.write, dataAccess]
    | mem a len => exact fun _ _ => rfl
    | xmm x =>
      exact Component.agrees_xmm_of_zmm (by simp only [popfState, Operand.write, dataAccess]) x
    | mxcsr => show _ = _; simp only [popfState, Operand.write, dataAccess]
    | fpr x =>
      exact Component.agrees_fpr_of_fp87 (by simp only [popfState, Operand.write, dataAccess]) x
    | fsw => show _ = _; simp only [popfState, Operand.write, dataAccess]
    | fcc => show _ = _; simp only [popfState, Operand.write, dataAccess]
    | ftw => show _ = _; simp only [popfState, Operand.write, dataAccess]
    | fcw => show _ = _; simp only [popfState, Operand.write, dataAccess]
    | fpuPtr => show _ = _; simp only [popfState, Operand.write, dataAccess, fpuPtrOf]
  · simp only [fixedPart, popfState, Operand.write, dataAccess, beforeFetch, resetStepFields,
      fixed_popf16Spec hk]

end X86Proofs
