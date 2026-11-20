import X86Proofs.Program.Effect

/-!
# The register file after an effect

An effect lists the registers it writes; these lemmas turn that into the whole general-purpose
register file after it (`t.GPR`), as `Vector.set` of the one written register
(`Effect.Holds.gprWrite`) or unchanged (`Effect.Holds.gprUnchanged`), so a run proof can track the
register file as a single value.
-/

namespace X86Proofs
open X86 X86.Machine X86.UserProcess

/-- A single full-register write determines the complete resulting register file. -/
theorem Effect.Holds.gprWrite {s t : RamState} {e : Effect} (h : e.Holds s t)
    (dst : BitVec 5) (value : BitVec 64) (hw : e.writes = [⟨.reg dst, value⟩]) :
    t.GPR = Vector.set s.GPR dst.toNat value (by exact dst.isLt) := by
  have hv : (Operand.reg dst : Operand 64).read t = value := by
    simpa only [hw, Write.AllHold] using h.writes
  apply Vector.ext
  intro i hi
  have hmod : i % 2^5 = i := Nat.mod_eq_of_lt hi
  by_cases he : i = dst.toNat
  · subst i
    simpa only [Operand.read_reg64, gprIndex, Fin.getElem_fin, Vector.getElem_set_self] using hv
  · have hr : (BitVec.ofNat 5 i) ≠ dst := by
      intro h; have heq := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, hmod] at heq
      exact he heq
    have hn : Component.reg (BitVec.ofNat 5 i) ∉ e.components := by
      simp only [Effect.components, hw, List.map_cons, List.map_nil, Write.component_reg,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      cases e.flags <;> simp [hr]
    have hv := h.agrees.read (n := 64) hn
    simpa only [Operand.read_reg64, gprIndex, Fin.getElem_fin, BitVec.toNat_ofNat,
      hmod, Vector.getElem_set, he, Ne.symm he, ite_false] using hv

/-- A frame with no general-purpose-register writes preserves that register file. -/
theorem AgreesExcept.gprUnchanged {s t : RamState} {cs : List Component} (h : AgreesExcept cs s t)
    (hw : ∀ r, Component.reg r ∉ cs) : t.GPR = s.GPR := by
  apply Vector.ext
  intro i hi
  have hmod : i % 2^5 = i := Nat.mod_eq_of_lt hi
  have hv := h.read (n := 64) (hw (BitVec.ofNat 5 i))
  simpa only [Operand.read_reg64, gprIndex, Fin.getElem_fin, BitVec.toNat_ofNat, hmod] using hv

/-- Effects without general-purpose-register writes preserve that register file. -/
theorem Effect.Holds.gprUnchanged {s t : RamState} {e : Effect} (h : e.Holds s t)
    (hw : ∀ r, Component.reg r ∉ e.components) : t.GPR = s.GPR := h.agrees.gprUnchanged hw

end X86Proofs
