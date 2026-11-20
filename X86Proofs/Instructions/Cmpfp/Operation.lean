import X86Proofs.Instructions.Cmpfs.Operation

/-!
# CMPPS, CMPPD specification

`CMPPS xmm1, xmm2/m128, imm8` (`NP 0F C2 /r ib`) and `CMPPD xmm1, xmm2/m128, imm8` (`66 0F C2 /r
ib`) compare the packed single- or double-precision elements lane by lane by the predicate in
imm8 bits 0–2 (EQ, LT, LE, UNORD, NEQ, NLT, NLE, ORD; `cmpPred`) and write all ones (true) or
all zeros (false) to each `e`-bit lane; every lane's exception flags, reduced to the invalid one
when it is raised (`FP.Prioritize_Operand_Exceptions`, `fpOperandPrio`), are ORed into MXCSR. Each
lane and its flags are lean-x86's own `FP.Compare5` at that MXCSR (`fpCompare5`,
`Core/Float.lean`); there is no IEEE-754 library to state them against independently.
`cmpfpSpec e mx a b imm` is the result, `cmpfpFlags e mx a b imm` the exception flags, `cmpfpOk e
mx a b imm` that lean-x86 returns every lane; lean-x86 computes both with `Operations.CMP3Pf e
128`.
-/

namespace X86Proofs

open X86 X86.Helpers X86.Runtime

/-- Lane `i` of the comparison and its flags. -/
def cmpfpLane (e : Nat) (mx : BitVec 32) (a b : BitVec 128) (imm : BitVec 8) (i : Nat) :
    BitVec e × BitVec 6 :=
  (cmpMask e (fpCompare5 e (cmpPred imm) mx (lane e a i) (lane e b i)).1,
    fpOperandPrio (fpCompare5 e (cmpPred imm) mx (lane e a i) (lane e b i)).2)

/-- The lane-by-lane comparison masks of `a` and `b` at MXCSR `mx`. -/
def cmpfpSpec (e : Nat) (mx : BitVec 32) (a b : BitVec 128) (imm : BitVec 8) : BitVec 128 :=
  fpPacked e (cmpfpLane e mx a b imm)

/-- The exception flags, every lane's ORed. -/
def cmpfpFlags (e : Nat) (mx : BitVec 32) (a b : BitVec 128) (imm : BitVec 8) : BitVec 6 :=
  fpPackedFlags e (cmpfpLane e mx a b imm)

/-- lean-x86's comparison returns a value on every lane (`FpCompare5Ok`). -/
def cmpfpOk (e : Nat) (mx : BitVec 32) (a b : BitVec 128) (imm : BitVec 8) : Prop :=
  ∀ i < 128 / e, FpCompare5Ok e (cmpPred imm) mx (lane e a i) (lane e b i)

theorem cmpfp_operation [X86.Machine.Bindings] (e : Nat) (he : e = 32 ∨ e = 64)
    (s : X86.Machine.RamState) (a b : BitVec 128) (imm : BitVec 8) (hm : MxcsrPre s)
    (hok : cmpfpOk e s.MXCSR a b imm) :
    (X86.Instructions.Operations.CMP3Pf e 128 a b imm).run s =
      (.ok (cmpfpSpec e s.MXCSR a b imm),
        { s with MXCSR := mxOr s.MXCSR (cmpfpFlags e s.MXCSR a b imm) }) := by
  rcases he with rfl | rfl <;> unfold X86.Instructions.Operations.CMP3Pf <;>
    fp_packed_start_minmax <;> simp only [cmpPred_eq]
  · fp_packed_loop_split 32
      (fun i r => (r.1 ||| fpOperandPrio
          (fpCompare5 32 (cmpPred imm) s.MXCSR (lane 32 a i) (lane 32 b i)).2,
        setSlice r.2 (i * 32) 32
          (if (fpCompare5 32 (cmpPred imm) s.MXCSR (lane 32 a i) (lane 32 b i)).1 then
            BitVec.allOnes 32 else 0)))
      (fun i hi => fpCompare5_run _ (by decide) _ _ _ _ (hok i hi)) hm
  · fp_packed_loop_split 64
      (fun i r => (r.1 ||| fpOperandPrio
          (fpCompare5 64 (cmpPred imm) s.MXCSR (lane 64 a i) (lane 64 b i)).2,
        setSlice r.2 (i * 64) 64
          (if (fpCompare5 64 (cmpPred imm) s.MXCSR (lane 64 a i) (lane 64 b i)).1 then
            BitVec.allOnes 64 else 0)))
      (fun i hi => fpCompare5_run _ (by decide) _ _ _ _ (hok i hi)) hm

end X86Proofs
