import X86Proofs.Core.Gpr
import X86Proofs.Core.ReadOnly
import X86Proofs.Program.ReadWrite.String

/-!
# CPUID specification

`CPUID` (Intel SDM): the processor's identification and feature information for leaf EAX and
subleaf ECX, returned in EAX, EBX, ECX and EDX (zero-extended into RAX, RBX, RCX, RDX). The answer
is the processor's (lean-x86's `Get_CPUID_Value` binding, `cpuidResult Bindings.processor`): it
depends on the leaf and subleaf and on XCR0 and CR4.OSXSAVE only, and is taken as given
(`cpuidResult … = .ok r`).

lean-x86 faults (#GP) when CPUID faulting is enabled (`PLATFORM_INFO.CPUID_FAULTING_EN`,
`FEATURE_ENABLES.CPUID_GP_ON_CPL_GT_0`) outside SMM at CPL > 0, and with
`IA32_MISC_ENABLE.LIMIT_CPUID_MAXVAL` set it answers leaf 2 for leaves above 2 and caps leaf 0's
maximum. `cpuid_operation` takes faulting disabled (`CPUID_FAULTING_EN = 0`) and the limit clear.
-/

namespace X86Proofs

open X86 X86.Machine X86.Helpers

/-- CPUID's write-back: RAX, RBX, RCX, RDX set to the four 32-bit answers `r` (EAX, EBX, ECX, EDX
order), each zero-extended, in that order. -/
def cpuidState (s : RamState) (r : Cpuid.Registers) : RamState :=
  (Operand.reg 2 : Operand 32).write ((Operand.reg 1 : Operand 32).write
    ((Operand.reg 3 : Operand 32).write ((Operand.reg 0 : Operand 32).write s r.1) r.2.1)
    r.2.2.1) r.2.2.2

theorem cpuid_operation [Bindings] (s : RamState) (hfault : s.PLATFORM_INFO.CPUID_FAULTING_EN = 0)
    (hlimit : s.IA32_MISC_ENABLE.LIMIT_CPUID_MAXVAL = 0) (r : Cpuid.Registers)
    (hr : cpuidResult Bindings.processor s ((Operand.reg 0 : Operand 32).read s)
      ((Operand.reg 1 : Operand 32).read s) = .ok r) :
    (X86.Instructions.Operations.CPUID : X86.Runtime.SpecM X86.Exception RamState Unit).run s =
      (.ok (), cpuidState s r) := by
  have hget := congrFun (congrFun (congrFun (getCPUIDValue_eq Bindings.processor)
    ((Operand.reg 0 : Operand 32).read s)) ((Operand.reg 1 : Operand 32).read s)) s
  rw [hr] at hget
  unfold X86.Instructions.Operations.CPUID
  spec_run []
  simp only [hfault, HAnd.hAnd, AndOp.and, strictAnd, BitVec.reduceBEq, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]
  spec_run [EAX => eax_run _, ECX => ecx_run _]
  simp only [hlimit, BitVec.reduceBEq, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  spec_run [ECX => ecx_run _,
    X86.Runtime.liftNoSourceException => specM_liftNoSourceException_run _ _ _ _ hget]
  simp only [hlimit, BitVec.reduceBEq, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  spec_run [Write_RAX => writeRAX_run _ 32 (by decide) _,
    Write_RBX => writeRBX_run _ 32 (by decide) _,
    Write_RCX => writeRCX32_run _ _]
  rw [writeRDX_run _ 32 (by decide)]
  simp only [cpuidState, rcx, Operand.write_reg64, Operand.write_reg_eq_set]
  rfl

end X86Proofs
