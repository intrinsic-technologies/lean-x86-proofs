import X86Proofs.Instructions.Movs.Step
import X86Proofs.Program.Effect
import X86Proofs.Program.Compose

/-!
# `movsb` triple

`movsb_triple`: `movsb` (`A4`) at `p`, derived by `Triple.of_effect` from `movsb_effect_step`
(from `movsb_step` and `movsb_ready`). Its postcondition is the effect `movsbEffect`, whose writes
include the byte at the old RDI, so the frame (`AgreesExcept`) names that byte and code and data
elsewhere are known to survive.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

/--
What `movsb` at `p` needs besides `ReadyToStep`: RIP = `p`, the direction flag clear, the source
byte (at RSI) and the destination byte (at RDI) below 4 GiB and present in RAM, and the
destination not a byte of the page-table entries (`PageTableEntriesApart`) nor the instruction's
own byte.
-/
structure MovsbPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat < 2^32
  srcMem : (s.external[rsi.read s]?).isSome
  dstLow : (rdi.read s).toNat < 2^32
  dstMem : (s.external[rdi.read s]?).isSome
  dstTables : PageTableEntriesApart (rdi.read s).toNat 1
  dstCode : rdi.read s ≠ p

/-- The effect of `movsb` at `p`, from state `s`: RIP = `p + 1`, RSI and RDI advanced by one,
and the byte at the old RDI set to the byte at the old RSI. The flags are untouched. -/
def movsbEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 1
  writes := [⟨rsi, rsi.read s + 1⟩, ⟨rdi, rdi.read s + 1⟩,
    ⟨(Operand.mem (rdi.read s) : Operand 8), (Operand.mem (rsi.read s) : Operand 8).read s⟩]

/-- `movsb` changes RSI, RDI, the byte at the old RDI and RIP. -/
@[simp] theorem movsbEffect_components (p : BitVec 64) (s : RamState) :
    (movsbEffect p s).components = [.reg 6, .reg 7, .mem (rdi.read s) 1, .rip] := by
  simp [movsbEffect, Effect.components]

/-- `movsb` at `p` does not overwrite its own byte if RDI ≠ `p`. -/
theorem movsbEffect_avoids {p : BitVec 64} {s : RamState} (hdst : rdi.read s ≠ p) :
    (movsbEffect p s).Avoids (codeRange p [0xA4]) := by
  intro x hx c hc hcov
  simp only [codeRange_cons, codeRange_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  simp only [movsbEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact hcov
  · exact hcov
  · obtain ⟨i, hi, he⟩ := hcov
    obtain rfl : i = 0 := by omega
    exact hdst ((BitVec.add_zero _).symm.trans he.symm)
  · exact hcov

/-- The step behind `movsb_triple`: from a ready state with the instruction in memory and the
precondition, one `step` reaches a ready state with the effect `movsbEffect`. -/
theorem movsb_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (MovsbPre p) (codeRange p [0xA4]) (movsbEffect p) := by
  intro s h hcode hpre
  have hdst : (rdi.read s).toNat + 1 ≤ 2^32 := by have := hpre.dstLow; omega
  have hcodeS : BytesAt s s.RIP [0xA4] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 1 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  refine ⟨_, movsb_step s h hpre.df hcodeS hlow (by have := hpre.srcLow; omega) hdst
    hpre.srcMem hpre.dstMem, movsb_ready h hdst hpre.dstTables,
    ⟨?_, ⟨movsbAfter_rsi s, movsbAfter_rdi s, movsbAfter_copy s⟩, trivial,
      ?_⟩⟩
  · rw [movsbAfter_rip h, hpre.rip]
    rfl
  · rw [movsbEffect_components]
    exact AgreesExcept.movsb s

/-- The triple for `movsb` at `p`: the effect `movsbEffect`. -/
theorem movsb_triple [Bindings] (p : BitVec 64) :
    Triple (MovsbPre p) (codeRange p [0xA4]) (Effect.post (movsbEffect p)) :=
  Triple.of_effect (fun _ hpre => movsbEffect_avoids hpre.dstCode)
    (movsb_effect_step p)
attribute [x86_compose] movsbEffect

@[x86_local] theorem movsbEffect_local {p : BitVec 64} :
    Effect.Local (movsbEffect p) := by
  effect_local [movsbEffect]

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem MovsbPre.of_holds (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p : BitVec 64} (hrip : e.rip = p)
    (hdf : (Operand.df : Operand 1).read (e.after s true) = 0#1)
    (hsrcLow : (rsi.read (e.after s true)).toNat < 2 ^ 32)
    (hsrcMem : (s.external[rsi.read (e.after s true)]?).isSome)
    (hdstLow : (rdi.read (e.after s true)).toNat < 2 ^ 32)
    (hdstMem : (s.external[rdi.read (e.after s true)]?).isSome)
    (hdstTables : PageTableEntriesApart (rdi.read (e.after s true)).toNat 1)
    (hdstCode : rdi.read (e.after s true) ≠ p) : MovsbPre p s' := by
  have hsi : rsi.read s' = rsi.read (e.after s true) := Obs.back_reg ho 6
  have hdi : rdi.read s' = rdi.read (e.after s true) := Obs.back_reg ho 7
  exact ⟨h.rip_of hrip, DirectionFlagClear.of_obs ho hdf, hsi ▸ hsrcLow,
    hsi ▸ h.present1 hsrcMem, hdi ▸ hdstLow, hdi ▸ h.present1 hdstMem, hdi ▸ hdstTables,
    hdi ▸ hdstCode⟩

end Carry

end X86Proofs
