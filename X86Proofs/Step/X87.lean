import X86Proofs.Step.Sse
import X86Proofs.Core.X87

namespace X86Proofs

open X86 X86.Machine X86.UserProcess X86.Helpers X86.Runtime

/-- With `CR0.EM` and `CR0.TS` clear, the x87 unit is enabled (no #NM). -/
theorem isEnabled_run {s : RamState} (h : Prelude.CR0.SSEEnabled s.CR0) :
    (FP87.Is_Enabled : SpecM X86.Exception RamState Bool).run s = (.ok true, s) := by
  unfold FP87.Is_Enabled
  spec_run [X86.CR0.EM => cr0EM_run_of_cr0 h, X86.CR0.TS => cr0TS_run_of_cr0 h]

/-- `CR0.MP` reads bit 1 of CR0. -/
theorem cr0MP_run (s : RamState) :
    (X86.CR0.MP : SpecM X86.Exception RamState _).run s = (.ok (s.CR0.extractLsb' 1 1), s) := by
  simp [X86.CR0.MP, x86_runtime, get, getThe, MonadStateOf.get, bind, pure, ExceptT.bind,
    ExceptT.run, ExceptT.mk, StateT.bind, ExceptT.bindCont, liftM, monadLift, MonadLift.monadLift,
    ExceptT.pure, StateT.pure, StateT.get, ExceptT.lift, Functor.map, StateT.map]

/-- `CPUID_FDP_EXCPTN_ONLY` reads the processor's FDP_EXCPTN_ONLY bit. -/
theorem cpuidFdpExcptnOnly_run [Bindings] {s : RamState} {b : Bool}
    (h : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding b) :
    (CPUID_FDP_EXCPTN_ONLY : SpecM X86.Exception RamState Bool).run s = (.ok b, s) := by
  unfold CPUID_FDP_EXCPTN_ONLY
  spec_run [X86.Runtime.liftNoSourceException => readCPUIDFeature_run h]

theorem nullSegment_ok (seg : Segment) : ∃ v, Null_Segment seg = .ok v := ⟨_, rfl⟩

/-- The null segment `Null_Segment seg` builds (selector and descriptor 0, the flags of `seg`). -/
def nullSegmentOf (seg : Segment) : Segment :=
  { selector := 0, descriptor := X86.Runtime.InitializedBits.ofValue 0,
    descriptor_high := X86.Runtime.InitializedBits.ofValue 0, descriptor_valid := some false,
    is_stack := seg.is_stack, is_code := seg.is_code,
    is_64bit_mode_data_segment := seg.is_64bit_mode_data_segment }

theorem nullSegment_eq (seg : Segment) : Null_Segment seg = .ok (nullSegmentOf seg) := rfl

/-- `FP87.Update_Instruction_Info` in 64-bit mode, with no pending exception (FSW.ES clear) on a
processor that updates FDP only on exceptions (CPUID FDP_EXCPTN_ONLY): FCS := the code segment's
selector, FIP := RIP (the address of the instruction); FDP, FDS and FOP are kept. -/
theorem updateInstructionInfo_run [Bindings] (s : RamState) (opcode modrm : BitVec 8)
    (hasMem : Bool) (seg : Segment) (off : BitVec 64) (hmode : In64BitMode s)
    (hes : fswES s.FP87_Status = 0)
    (hfdp : Prelude.ReportsCPUFeature Bindings.processor s CPUID_FDP_EXCPTN_ONLY_Encoding true) :
    (FP87.Update_Instruction_Info opcode modrm hasMem seg off :
        SpecM X86.Exception RamState Unit).run s =
      (.ok (), { s with FP87_FCS := s.CS.selector, FP87_FIP := s.RIP }) := by
  unfold FP87.Update_Instruction_Info
  have hst : ∀ (fcs : BitVec 16) (fip : BitVec 64),
      SameControls s { s with FP87_FCS := fcs, FP87_FIP := fip } :=
    fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hfdp' := fun fcs fip => reportsCPUFeature_of_sameControls (hst fcs fip) hfdp
  have hst' : SameControls s { s with FP87_FCS := s.CS.selector } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hmode' : In64BitMode { s with FP87_FCS := s.CS.selector } := hmode.of_cs_lma_eq rfl rfl
  cases hc : (Config.Value.Feature_FIP_Use_Linear_Address.value : Bool)
  · have hcfg : ∀ t : RamState, (liftM (Config.Read.Feature_FIP_Use_Linear_Address
        (exception := X86.Exception)) : SpecM X86.Exception RamState Bool).run t =
          (.ok false, t) := by
      intro t
      show (Config.Read.Feature_FIP_Use_Linear_Address, t) = _
      unfold Config.Read.Feature_FIP_Use_Linear_Address; rw [hc]; rfl
    spec_run [liftM => hcfg _, X86.FP87_Status.ES => fp87StatusES_run _,
      X86.CPUID_FDP_EXCPTN_ONLY => cpuidFdpExcptnOnly_run (hfdp' _ _)]
    simp only [hes]
    rfl
  · have hcfg : ∀ t : RamState, (liftM (Config.Read.Feature_FIP_Use_Linear_Address
        (exception := X86.Exception)) : SpecM X86.Exception RamState Bool).run t =
          (.ok true, t) := by
      intro t
      show (Config.Read.Feature_FIP_Use_Linear_Address, t) = _
      unfold Config.Read.Feature_FIP_Use_Linear_Address; rw [hc]; rfl
    simp only [bind_assoc]
    spec_run [liftM => hcfg _, X86.Helpers.In_64Bit_Mode => hmode',
      X86.FP87_Status.ES => fp87StatusES_run _,
      X86.CPUID_FDP_EXCPTN_ONLY => cpuidFdpExcptnOnly_run (hfdp' _ _)]
    simp only [hes]
    rfl


/-- lean-x86's `Obsolete_X87_NOP` (FENI, FDISI, FSETPM) without a LOCK prefix and with the x87 unit
enabled: `Next_IP` := `ip`, nothing else. -/
theorem obsoleteX87Nop_run [Bindings] (s : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (hlock : ctx.lock_prefix_present = false) (hcr0 : Prelude.CR0.SSEEnabled s.CR0) :
    (X86.Instructions.Obsolete_X87_NOP ip ctx).run s = (.ok (), withNextIP s ip) := by
  unfold X86.Instructions.Obsolete_X87_NOP
  simp only [hlock]
  spec_run [FP87.Is_Enabled => isEnabled_run hcr0]

end X86Proofs
