import InitECandidate.Solver.Wave8Stage.Stage4AllocGlue
import InitECandidate.Solver.Wave8Stage.Stage4FullInitSafety
import InitECandidate.Solver.Wave8Stage.ConcreteStackLayout
import InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.PanInstallation
import InitECandidate.Solver.Wave8Stage.ConcreteCompilerWord
import InitE.SourceNameFacts

/-!
# `InitECandidate.Solver.Wave8Stage.R12_Stage4BoundArgon`

Self-contained concrete Stage 4 (`StackSem -> LabSem`) initialization, memory
safety, affine transfer, `codeStepBudget` reduction, and target budget
arithmetic for the `InitECandidate` pipeline without importing `FastBaselineEnv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.R12_Stage4BoundArgon

open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Pancake.Proofs.PanToTarget
open InitECandidate.Solver.FastEnv
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.Wave8Stage.RuntimeLabels
open InitECandidate.Solver.Wave8Stage.Stage4
open InitECandidate.Solver.Wave8Stage.StackToLabClock
open InitECandidate.Solver.Wave8Stage.Static
open PanToStackRawCallNoAllocAndStackAllocStructural
open PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc
open StackToLabAndLabToTargetNoLocValue6

/-! ## 1. ArtifactEnv Bridge (Zero `FastBaselineEnv` Dependency) -/

theorem baselineNames_eq :
    InitECandidate.Solver.FastEnv.baselineNames =
      InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baselineNames := by
  unfold InitECandidate.Solver.FastEnv.baselineNames
    InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baselineNames
  rfl

theorem baselineMmio_eq :
    InitECandidate.Solver.FastEnv.baselineMmio =
      InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baselineMmio := by
  unfold InitECandidate.Solver.FastEnv.baselineMmio
    InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baselineMmio
  rfl

theorem baselineMachineConfig_eq :
    InitECandidate.Solver.FastEnv.baselineMachineConfig =
      InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baselineMachineConfig := by
  unfold InitECandidate.Solver.FastEnv.baselineMachineConfig
    InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baselineMachineConfig
  rw [baselineNames_eq, baselineMmio_eq]; rfl

theorem baselineInstalledState_eq :
    InitECandidate.Solver.FastEnv.baselineInstalledState =
      InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baselineInstalledState := rfl

theorem fastEnv_baseline_machine_isRiscv : isRiscvMachineConfig baselineMachineConfig := by
  rw [baselineMachineConfig_eq]
  exact InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baseline_machine_isRiscv

theorem fastEnv_baseline_pan_installed_core :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      (some baselineNames) (11, 13) baselineMachineConfig baselineMmio baselineInstalledState
      (wlabWlocExact ∘ sourceMemory) ordinaryDomain sharedDomain := by
  rw [baselineNames_eq, baselineMachineConfig_eq, baselineMmio_eq, baselineInstalledState_eq]
  exact InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baseline_pan_installed_core

theorem fastEnv_baseline_good_init :
    goodInitState baselineMachineConfig baselineInstalledState InitECandidate.nativeCode 3788
      installedAsm (packedWordMemory installedMemory)
      InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baselineDataDm
      InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baselineSharedDm := by
  rw [baselineMachineConfig_eq, baselineInstalledState_eq]
  exact InitECandidate.Solver.Wave8GuestInv.ArtifactEnv.baseline_good_init

/-! ## 2. Concrete Stage 4 Initial States and `FullMakeInit` Safety -/

noncomputable abbrev labState (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapDm sharedDm : BitVec 64 → Bool)
    (ltconf : LabToTarget.Config) (code : List (Nat × HolProg 64)) :=
  LabToTarget.makeInit (C := LabToTarget.Config) baselineMachineConfig (sourceFfi input) t m
    (fun a => (decide
      (t.regs (StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 2) ≤ a ∧
       a < t.regs (StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 4)) ||
      bitmapDm a) && holByteAligned a)
    (fun a => sharedDm a && holByteAligned a) baselineInstalledState
    (StackToLab.compile (oracleCompilerConfig oracles).stackConf
      (oracleCompilerConfig oracles).dataConf
      (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset code)
    (LabToTarget.compile riscvConfig)
    (baselineMachineConfig.target.getPc baselineInstalledState +
      BitVec.ofNat 64 InitECandidate.nativeCode.length) 3788
    (fun _ => (ltconf, StackToLab.compileNoStubs
      (oracleCompilerConfig oracles).stackConf.regNames
      (oracleCompilerConfig oracles).stackConf.jump riscvConfig.addrOffset
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) []))

noncomputable abbrev initialized (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapDm sharedDm : BitVec 64 → Bool)
    (ltconf : LabToTarget.Config) (code : List (Nat × HolProg 64)) :=
  FullMakeInit.fullMakeInit (oracleCompilerConfig oracles).stackConf
    (oracleCompilerConfig oracles).dataConf
    (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps code (labState oracles input t m bitmapDm sharedDm ltconf code)
    (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0 (fun _ => (ltconf, [], []))

theorem labState_eq_pipelineLabInitState (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapDm sharedDm : BitVec 64 → Bool)
    (ltconf : LabToTarget.Config) (code : List (Nat × HolProg 64)) :
    labState oracles input t m bitmapDm sharedDm ltconf code =
      pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig (sourceFfi input)
        t m bitmapDm sharedDm baselineInstalledState InitECandidate.nativeCode 3788 ltconf code := rfl

theorem initialized_fst_eq_pipelineStackInitState (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapDm sharedDm : BitVec 64 → Bool)
    (ltconf : LabToTarget.Config) (code : List (Nat × HolProg 64)) :
    (initialized oracles input t m bitmapDm sharedDm ltconf code).1 =
      pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig (sourceFfi input)
        t m bitmapDm sharedDm baselineInstalledState InitECandidate.nativeCode 3788 ltconf
        InitECandidate.bitmaps code 0 := rfl

/-- Concrete `FullMakeInitSemantics.Assumptions`, `fullMakeInit` success, and
`MemorySafe` for the installed `InitECandidate` artifact. -/
theorem concrete_assumptions (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (code : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config)
    (hwtw : WordToWord.compile (oracleCompilerConfig oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wordCode))
    (hwts : WordToStack.Native.compileNative riscvConfig false wordCode =
      (InitECandidate.bitmaps, wconf, fs, code)) :
    ∃ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
      (bitmapDm sharedDm : BitVec 64 → Bool)
      (aux : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory),
      (∀ a, ordinaryDomain a → m a = wlabWlocExact (sourceMemory a)) ∧
      (sharedDomain = fun a => sharedDm a = true ∧ holByteAligned a = true) ∧
      goodInitState baselineMachineConfig baselineInstalledState InitECandidate.nativeCode
        3788 t m (fun a => decide
          (t.regs (StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 2) ≤ a ∧
           a < t.regs (StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 4)) ||
          bitmapDm a) sharedDm ∧
      let lab := labState oracles input t m bitmapDm sharedDm ltconf code
      FullMakeInitSemantics.Assumptions (oracleCompilerConfig oracles).stackConf
        (oracleCompilerConfig oracles).dataConf
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
        InitECandidate.bitmaps code lab
        (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0
        (fun _ => (ltconf, [], [])) ∧
      initialized oracles input t m bitmapDm sharedDm ltconf code =
        ((initialized oracles input t m bitmapDm sharedDm ltconf code).1, some aux) ∧
      MemorySafe storeConstsStubLocation lab.memDomain lab.memory := by
  obtain ⟨t, m, bitmapPtr, bitmapDm, sharedDm, hm, hgi, hshared,
    ha2, ha4, hab, horder, hspace, hdisjoint, hm0, hm1, hm2, hm3, hm4, hbitmap, _, _⟩ :=
    fastEnv_baseline_pan_installed_core
  have hnames :
      StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 2 = 11 ∧
      StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 4 = 13 := by
    simp only [oracleCompilerConfig, pancakeRiscVBackendConfig_eq, riscvBackendConfig_eq_executable]
    decide_cbv
  have hA := panToTargetFullMakeInitAssumptions
    (oracleCompilerConfig oracles) baselineMachineConfig (sourceFfi input) t m bitmapPtr
    bitmapDm sharedDm baselineInstalledState (LabToTarget.compile riscvConfig)
    InitECandidate.nativeCode 3788 ltconf sourceDeclarations col wordCode
    InitECandidate.bitmaps wconf fs code 0 (oracleBackendConfigOk oracles)
    (riscvMachineConfigOk _ fastEnv_baseline_machine_isRiscv)
    (oracleMachineInitOk oracles _ fastEnv_baseline_machine_isRiscv) (by decide)
    hwtw hwts sourceDistinctFunctions
    (by simpa only [hnames.1, hnames.2] using
      And.intro ha2 ⟨ha4, hab, horder, hspace, hdisjoint, hm0, hm1, hm2, hm3, hm4, hbitmap⟩)
  change FullMakeInitSemantics.Assumptions _ _ _ _ _ _ _
    (labState oracles input t m bitmapDm sharedDm ltconf code) _ _ _ at hA
  have hsuccess : (initialized oracles input t m bitmapDm sharedDm ltconf code).2 ≠ none := by
    exact (FullMakeInitSemantics.fullMakeInitSemantics
      ⟨(show FullMakeInit.fullMakeInit _ _ _ _ _ _ _ _ _ _ _ =
          ((initialized oracles input t m bitmapDm sharedDm ltconf code).1,
           (initialized oracles input t m bitmapDm sharedDm ltconf code).2) from rfl), hA⟩).1
  obtain ⟨aux, haux⟩ := Option.ne_none_iff_exists'.mp hsuccess
  refine ⟨t, m, bitmapDm, sharedDm, aux, hm, hshared, ?_, hA, ?_, ?_⟩
  · simpa only [hnames.1, hnames.2] using hgi
  · exact Prod.ext rfl haux
  · apply memorySafe_of_goodInitState storeConstsStubLocation _ _ _ _ t m _ _ _ hgi
    intro a ha; change (_ && holByteAligned a) = true at ha; simp only [Bool.and_eq_true] at ha; exact ha.2

/-! ## 3. Concrete Stage 4 (`StackSem -> LabSem`) Affine Transfer -/

/-- Concrete Stage 4 transfer from `StackSem` to `LabSem` on the installed
`InitECandidate` artifact, with explicit procedure-step budget `M`. -/
theorem lab_transfer_exists (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (code : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config)
    (hwtw : WordToWord.compile (oracleCompilerConfig oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wordCode))
    (hwts : WordToStack.Native.compileNative riscvConfig false wordCode =
      (InitECandidate.bitmaps, wconf, fs, code)) :
    ∃ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
      (bitmapDm sharedDm : BitVec 64 → Bool)
      (aux : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory),
      let lab := labState oracles input t m bitmapDm sharedDm ltconf code
      let init := initialized oracles input t m bitmapDm sharedDm ltconf code
      let M := codeStepBudget (FullMakeInitSemantics.code2
        (oracleCompilerConfig oracles).stackConf (oracleCompilerConfig oracles).dataConf
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset code)
      (∀ a, ordinaryDomain a → m a = wlabWlocExact (sourceMemory a)) ∧
      (sharedDomain = fun a => sharedDm a = true ∧ holByteAligned a = true) ∧
      goodInitState baselineMachineConfig baselineInstalledState InitECandidate.nativeCode
        3788 t m (fun a => decide
          (t.regs (StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 2) ≤ a ∧
           a < t.regs (StackNames.findNameSpt (oracleCompilerConfig oracles).stackConf.regNames 4)) ||
          bitmapDm a) sharedDm ∧
      init = (init.1, some aux) ∧
      ∀ k : Nat,
        let res := (StackSemEvaluate.evaluate
          ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
            { init.1 with clock := k })).1
        FlattenSemantics.stackEntryClass res ≠ .RunError →
        res ≠ some .timeOut →
        (LabSem.evaluate { lab with clock := 2 * (M + 1) * k + (3 * M + 2) }).1 ≠ .timeOut := by
  obtain ⟨t, m, bitmapDm, sharedDm, aux, hm, hshared, hgi, hA, hinit, hsafe⟩ :=
    concrete_assumptions oracles input col wordCode wconf fs code ltconf hwtw hwts
  refine ⟨t, m, bitmapDm, sharedDm, aux, hm, hshared, hgi, hinit, ?_⟩
  intro k res hne hnt
  have hcode : code = (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile (oracleCompilerConfig oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations)).2).2.2.2 := by rw [hwtw, hwts]
  exact fullMakeInit_lab_affine_of_source_run
    (oracleCompilerConfig oracles).stackConf (oracleCompilerConfig oracles).dataConf
    (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps code (labState oracles input t m bitmapDm sharedDm ltconf code)
    (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0
    (fun _ => (ltconf, [], [])) hA riscvConfig false
    (oracleCompilerConfig oracles).wordToWordConf riscvConfig.isa sourceDeclarations
    hcode hsafe (fun _ => rfl) k hne hnt

/-- Direct Stage 4 transfer for any `goodInitState` and `FullMakeInitSemantics.Assumptions`
formulated in terms of `pipelineStackInitState` and `pipelineLabInitState`, plus monotonicity
in an upper bound `M_bound` on `codeStepBudget`. -/
theorem stage4_stack_to_lab_bounded_not_timeOut
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64) (bitmapDm sharedDm : BitVec 64 → Bool)
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (code : List (Nat × HolProg 64)) (ltconf : LabToTarget.Config)
    (hwtw : WordToWord.compile (oracleCompilerConfig oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wordCode))
    (hwts : WordToStack.Native.compileNative riscvConfig false wordCode =
      (InitECandidate.bitmaps, wconf, fs, code))
    (hgi : goodInitState baselineMachineConfig baselineInstalledState InitECandidate.nativeCode
      3788 t m (ConcreteInitMemory.dataDomain oracles t bitmapDm) sharedDm)
    (hA : FullMakeInitSemantics.Assumptions (oracleCompilerConfig oracles).stackConf
      (oracleCompilerConfig oracles).dataConf
      (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      InitECandidate.bitmaps code
      (pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig (sourceFfi input)
        t m bitmapDm sharedDm baselineInstalledState InitECandidate.nativeCode 3788 ltconf code)
      (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0
      (fun _ => (ltconf, [], [])))
    (M_bound k : Nat)
    (hM : codeStepBudget (FullMakeInitSemantics.code2
      (oracleCompilerConfig oracles).stackConf (oracleCompilerConfig oracles).dataConf
      (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset code) ≤ M_bound)
    (hne : FlattenSemantics.stackEntryClass
      (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
          { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
              (sourceFfi input) t m bitmapDm sharedDm baselineInstalledState
              InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps code 0 with clock := k })).1 ≠ .RunError)
    (hnt : (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
          { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
              (sourceFfi input) t m bitmapDm sharedDm baselineInstalledState
              InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps code 0 with clock := k })).1 ≠ some .timeOut) :
    (LabSem.evaluate
      { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig (sourceFfi input)
          t m bitmapDm sharedDm baselineInstalledState InitECandidate.nativeCode 3788 ltconf code with
        clock := 2 * (M_bound + 1) * k + (3 * M_bound + 2) }).1 ≠ .timeOut := by
  let lab := pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
    (sourceFfi input) t m bitmapDm sharedDm baselineInstalledState InitECandidate.nativeCode 3788 ltconf code
  let M := codeStepBudget (FullMakeInitSemantics.code2
    (oracleCompilerConfig oracles).stackConf (oracleCompilerConfig oracles).dataConf
    (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset code)
  have hsafe : MemorySafe storeConstsStubLocation lab.memDomain lab.memory := by
    apply memorySafe_of_goodInitState storeConstsStubLocation _ _ _ _ t m _ _ _ hgi
    intro a ha; change (_ && holByteAligned a) = true at ha; simp only [Bool.and_eq_true] at ha; exact ha.2
  have hcode : code = (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile (oracleCompilerConfig oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations)).2).2.2.2 := by rw [hwtw, hwts]
  have hrun := fullMakeInit_lab_affine_of_source_run
    (oracleCompilerConfig oracles).stackConf (oracleCompilerConfig oracles).dataConf
    (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig oracles).dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps code lab (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0
    (fun _ => (ltconf, [], [])) hA riscvConfig false
    (oracleCompilerConfig oracles).wordToWordConf riscvConfig.isa sourceDeclarations
    hcode hsafe (fun _ => rfl) k hne hnt
  dsimp only at hrun
  have hle : 2 * (M + 1) * k + (3 * M + 2) ≤ 2 * (M_bound + 1) * k + (3 * M_bound + 2) := by
    have h1 : 2 * (M + 1) ≤ 2 * (M_bound + 1) := by omega
    have h2 : 2 * (M + 1) * k ≤ 2 * (M_bound + 1) * k := Nat.mul_le_mul_right k h1
    omega
  rcases hev : LabSem.evaluate { lab with clock := 2 * (M + 1) * k + (3 * M + 2) } with ⟨res, st'⟩
  have hnt' : res ≠ .timeOut := by change (res, st').1 ≠ .timeOut; rw [← hev]; exact hrun
  have hlift := LabProps.evaluateAddClock { lab with clock := 2 * (M + 1) * k + (3 * M + 2) } res st'
    (2 * (M_bound + 1) * k + (3 * M_bound + 2) - (2 * (M + 1) * k + (3 * M + 2))) ⟨hev, hnt'⟩
  have hsum : 2 * (M + 1) * k + (3 * M + 2) +
      (2 * (M_bound + 1) * k + (3 * M_bound + 2) - (2 * (M + 1) * k + (3 * M + 2))) =
      2 * (M_bound + 1) * k + (3 * M_bound + 2) := Nat.add_sub_of_le hle
  simp only [hsum] at hlift; rw [hlift]; exact hnt'

/-! ## 4. Stage 4 / Target Budget Arithmetic (`M = 7313`, `K_target`) -/

/-- Exact affine decomposition of the R10/R12 target clock budget:
with `bootstrapSteps = 23077`, `M = 7313`, and `stackClock = 2 * (449 * k_pan + 452)`,
the end-to-end target clock equals `118223496 * k_pan + 119233963`. -/
theorem target_clock_decomposition (k_pan : Nat) :
    23077 + 9 * (2 * (7313 + 1) * (2 * (449 * k_pan + 452)) + (3 * 7313 + 2) + 1) =
      118223496 * k_pan + 119233963 := by omega

/-- Monotonicity of the target clock budget when `M ≤ 7313` and `k_stack ≤ 2 * (449 * k_pan + 452)`. -/
theorem target_clock_le_of_bounds (M k_stack k_pan : Nat)
    (hM : M ≤ 7313) (hstack : k_stack ≤ 2 * (449 * k_pan + 452)) :
    23077 + 9 * (2 * (M + 1) * k_stack + (3 * M + 2) + 1) ≤
      118223496 * k_pan + 119233963 := by
  have h1 : 2 * (M + 1) ≤ 2 * (7313 + 1) := by omega
  have h2 : 2 * (M + 1) * k_stack ≤ 2 * (7313 + 1) * (2 * (449 * k_pan + 452)) :=
    Nat.mul_le_mul h1 hstack
  omega

end InitECandidate.Solver.Wave8Stage.R12_Stage4BoundArgon
