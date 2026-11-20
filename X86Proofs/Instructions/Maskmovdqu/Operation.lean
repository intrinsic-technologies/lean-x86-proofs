import X86Proofs.Program.ReadWrite.MaskStore
import X86Proofs.Program.ReadWrite.String

/-!
# MASKMOVDQU specification

`MASKMOVDQU xmm1, xmm2` (`66 0F F7 /r`): store the bytes of `xmm1` whose corresponding byte of
`xmm2` has its most significant bit set to the 16 bytes at DS:RDI (a segment prefix may replace
DS), with a non-temporal hint; the other bytes are not written. `maskmovdquSpec src mask old`: the
16 bytes at RDI afterwards, from their old value `old`.
-/

namespace X86Proofs

open X86 X86.Machine

/-- Byte `i` of the result is byte `i` of `src` if bit 7 of byte `i` of `mask` is set, else the
old byte `i`. -/
def maskmovdquSpec (src mask old : BitVec 128) : BitVec 128 :=
  ofLanes 128 8 fun i => if (lane 8 mask i).msb then lane 8 src i else lane 8 old i

open X86 X86.Machine X86.UserProcess X86.Helpers

theorem maskmovdquSpec_eq (src mask old : BitVec 128) :
    maskmovdquSpec src mask old = maskMerge src mask old := rfl

theorem extractLsb'_seven_beq_one (x : BitVec 8) : (x.extractLsb' 7 1 == 1) = x.msb := by
  rw [BitVec.msb_eq_getLsbD_last]
  have h : x.extractLsb' 7 1 = BitVec.ofBool (x.getLsbD 7) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 := by omega
    subst this
    simp
  rw [h]
  cases x.getLsbD 7 <;> rfl

theorem maskmovdqu_operation [Bindings] (t : RamState) (h : DataReady t)
    (ctx : Instruction_Context) (hm64 : ctx.is_mode64 = true)
    (hds : t.DS = {userStackSegment with is_stack := some false}) (hss : t.SS = userStackSegment)
    (hsr : ctx.seg_prefix_present = true → SegReady ctx.segment) (src mask : BitVec 128)
    (hw : MemWritable t (segAddr ctx (rdi.read t)) 16) :
    (X86.Instructions.Operations.MASKMOVDQU 64 ctx src mask).run t =
      (.ok (), maskStores (segAddr ctx (rdi.read t)) src mask
        { t with oracle := oracleSkip (oracleSkip t.oracle 464) 464 }) := by
  have heff : effSegment ctx t.DS = ctxSegment ctx false := effSegment_stack t hds hss ctx false
  have hseg (d : BitVec 64) :
      SegAccess (effSegment ctx t.DS) (rdi.read t + d) (segAddr ctx (rdi.read t) + d) := by
    rw [heff, ← segAddr_add]
    exact SegAccess.ctx hsr false _
  have hlow := hw.low
  have hs0 : SegAccess (effSegment ctx t.DS) (rdi.read t) (segAddr ctx (rdi.read t)) := by
    rw [heff]
    exact SegAccess.ctx hsr false _
  have hc1 := checkLogicalAddressIsWritable_run_seg t h _ _ _ hs0 64 (by decide) (by omega)
  have hc2 := checkLogicalAddressIsWritable_run_seg _ (h.oracle (oracleSkip t.oracle 464)) _ _ _
    (hseg (BitVec.ofInt 64 8)) 64 (by decide) (by
      rw [show BitVec.ofInt 64 8 = 8#64 from rfl, BitVec.toNat_add]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega)
  unfold X86.Instructions.Operations.MASKMOVDQU
  simp (config := { decide := true }) only [assert_of_true, pure_bind]
  refine (specM_bind_run _ _ (s := t) (value := 16) rfl).trans ?_
  refine (specM_bind_run _ _ (get_run t)).trans ?_
  refine (specM_bind_run _ _ (s := t) (value := effSegment ctx t.DS)
    (by rw [getEffectiveSegment_run_eff ctx t.DS hm64]; rfl)).trans ?_
  refine (specM_bind_run _ _ (rdiSlice_run t)).trans ?_
  refine (specM_bind_run _ _ (zeroExtend64_run _ _)).trans ?_
  refine (specM_bind_run _ _ hc1).trans ?_
  refine (specM_bind_run _ _ (addInt64_run _ _ _)).trans ?_
  refine (specM_bind_run _ _ hc2).trans ?_
  rw [show X86.Runtime.intRange 0 (16 - 1) =
    (List.range 16).map (fun i : Nat => (0 : Int) + (i : Int)) from rfl]
  refine (specM_bind_run _ _ (specM_forIn_foldl_run _ _
    (fun (x : Int) u => maskByteStoreN (segAddr ctx (rdi.read t)) src mask x.toNat u)
    (fun u => DataReady u ∧
      ∀ j < 16, (u.external[segAddr ctx (rdi.read t) + BitVec.ofNat 64 j]?).isSome)
    { t with oracle := oracleSkip (oracleSkip t.oracle 464) 464 } ⟨h.oracle _, hw.mem⟩
    ?_ ?_)).trans ?_
  · intro x hx u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' := List.mem_range.mp hk
    simp (disch := omega) only [x86_runtime, pure_bind]
    have ha : (0 + (k : Int)) * 8 ≤ 120 := by omega
    have hk8 : ((0 + (k : Int)) * 8).toNat = k * 8 := by omega
    have hkn : (0 + (k : Int)).toNat = k := by omega
    have hofs : BitVec.ofInt 64 (0 + (k : Int)) = BitVec.ofNat 64 k := by
      rw [Int.zero_add, BitVec.ofInt_natCast]
    simp only [ha, decide_true, assert_of_true, pure_bind]
    rw [hk8, hkn, show (mask.extractLsb' (k * 8) 8) = lane 8 mask k from rfl,
      extractLsb'_seven_beq_one, show (lane 8 mask k).msb = maskBitN mask k from rfl]
    unfold maskByteStoreN
    cases hb : maskBitN mask k
    · rfl
    · simp only [ite_true]
      refine (specM_bind_run _ _ (s := u) rfl).trans ?_
      rw [hofs]
      have hkl : (segAddr ctx (rdi.read t) + BitVec.ofNat 64 k).toNat =
          (segAddr ctx (rdi.read t)).toNat + k := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
          Nat.mod_eq_of_lt (by omega)]
      have hwr := logicalMemWrite_run_seg_align u hu.1 _ _ _ (hseg (BitVec.ofNat 64 k)) 8
        (by decide) (lane 8 src k) .Normal_Alignment (AlignmentOk.normal _ _) (by omega)
        (fun i hi => by
          rw [show i = 0 by omega]
          simpa using hu.2 k hk') true
      refine (specM_bind_run _ _ hwr).trans ?_
      rfl
  · intro x hx u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' := List.mem_range.mp hk
    have hkn : (0 + (k : Int)).toNat = k := by omega
    simp only [hkn]
    unfold maskByteStoreN
    split
    · have hkl : (segAddr ctx (rdi.read t) + BitVec.ofNat 64 k).toNat =
          (segAddr ctx (rdi.read t)).toNat + k := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
          Nat.mod_eq_of_lt (by omega)]
      have htab := hw.tables
      refine ⟨(hu.1.dataAccess "store").of_sameControls
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl
        (IdentityPageTableMemory.memStore hu.1.tables _ _ (by omega)
          (by omega)), fun j hj => memStore_isSome _ _ _ _ (hu.2 j hj)⟩
    · exact hu
  · rw [List.foldl_map]
    simp only [Int.zero_add, Int.toNat_natCast]
    rw [maskStoresN_eq_foldl]
    rfl

end X86Proofs
