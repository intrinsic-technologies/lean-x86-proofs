import X86Proofs.Instructions.Popf.Operation
import X86Proofs.Program.Compose

/-!
# POPF/POPFQ preconditions after a block

The carry-over lemmas of `PopfqPre` and `PopfPre` (`@[x86_pre]`), apart from the specification so
that `Operation.lean` does not import the composition layer.
-/

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers

section Carry

variable {e : Effect} {s s' : RamState}

@[x86_pre] theorem PopfqPre.of_holds (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p : BitVec 64} (hrip : e.rip = p)
    (hr : MemReadable s ((Operand.reg 4 : Operand 64).read (e.after s true)) 8)
    (hiopl : X86.Runtime.Unsigned (s.RFLAGS.extractLsb' 12 2) < s.CPL)
    (hkeeps : PopfKeeps ((Operand.mem ((Operand.reg 4 : Operand 64).read (e.after s true)) :
      Operand 64).read (e.after s true)) s.RFLAGS) : PopfqPre p s' := by
  have hsp : stackPtr s' = (Operand.reg 4 : Operand 64).read (e.after s true) := by
    rw [stackPtr_eq_read, Obs.back_reg ho]
  refine ⟨h.rip_of hrip, hsp ▸ hr.of_holds h, by rw [h.iopl_eq, h.CPL_eq]; exact hiopl, ?_⟩
  rw [hsp, Obs.back_mem ho]
  exact ⟨hkeeps.tf.trans (h.rflags_getLsbD (by decide)).symm,
    hkeeps.nt.trans (h.rflags_getLsbD (by decide)).symm,
    hkeeps.ac.trans (h.rflags_getLsbD (by decide)).symm,
    hkeeps.id.trans (h.rflags_getLsbD (by decide)).symm⟩

@[x86_pre] theorem PopfPre.of_holds (h : e.Holds s s') (ho : Obs (e.after s true) s')
    {p : BitVec 64} (hrip : e.rip = p)
    (hr : MemReadable s ((Operand.reg 4 : Operand 64).read (e.after s true)) 2)
    (hiopl : X86.Runtime.Unsigned (s.RFLAGS.extractLsb' 12 2) < s.CPL)
    (hkeeps : Popf16Keeps ((Operand.mem ((Operand.reg 4 : Operand 64).read (e.after s true)) :
      Operand 16).read (e.after s true)) s.RFLAGS) : PopfPre p s' := by
  have hsp : stackPtr s' = (Operand.reg 4 : Operand 64).read (e.after s true) := by
    rw [stackPtr_eq_read, Obs.back_reg ho]
  refine ⟨h.rip_of hrip, hsp ▸ hr.of_holds h, by rw [h.iopl_eq, h.CPL_eq]; exact hiopl, ?_⟩
  rw [hsp, Obs.back_mem ho]
  exact ⟨hkeeps.tf.trans (h.rflags_getLsbD (by decide)).symm,
    hkeeps.nt.trans (h.rflags_getLsbD (by decide)).symm⟩

end Carry

end X86Proofs
