import InitECandidate.Solver.FastBaselineEnv
import InitECandidate.Proofs.CompilerOracles
import InitE.SourceNameFacts
import InitECandidate.Solver.Wave8Stage.Stage4FullInitSafety

/-! The concrete installed machine supplies the initialization premises used
by the integration branch. Compiler equations remain the original equations;
neither initializer success nor a synthetic initial-state equality is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteInitialization
open Classical InitE Flapjack
open Compiler.Backend Compiler.Backend.RiscVConfig Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target
open Pancake.Proofs.PanToTarget StackToLab.Proofs
open InitECandidate.Solver.FastEnv RuntimeLabels

/-- The unfiltered pipeline Lab state, with the original installed machine,
native bytes, code-buffer size, aligned domains and empty compile oracle. -/
noncomputable def labState (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapDm sharedDm : BitVec 64 → Bool) (ltconf : LabToTarget.Config)
    (code : List (Nat × StackLang.HolProg 64)) :
    LabSem.State 64 LabToTarget.Config Guest.HostMemory :=
  let c := oracleCompilerConfig oracles
  let sp := riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)
  let maxHeap := 2 * DataToWord.maxHeapLimit 64 c.dataConf - 1
  let heapDm := fun a => decide
    (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ a ∧
     a < t.regs (StackNames.findNameSpt c.stackConf.regNames 4))
  LabToTarget.makeInit baselineMachineConfig (sourceFfi input) t m
    (fun a => (heapDm a || bitmapDm a) && holByteAligned a)
    (fun a => sharedDm a && holByteAligned a) baselineInstalledState
    (StackToLab.compile c.stackConf c.dataConf maxHeap sp riscvConfig.addrOffset code)
    (LabToTarget.compile riscvConfig)
    (baselineMachineConfig.target.getPc baselineInstalledState +
      BitVec.ofNat 64 InitECandidate.nativeCode.length) 3788
    (fun _ => (ltconf, StackToLab.compileNoStubs c.stackConf.regNames
      c.stackConf.jump riscvConfig.addrOffset sp []))

noncomputable def initialized (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapDm sharedDm : BitVec 64 → Bool) (ltconf : LabToTarget.Config)
    (code : List (Nat × StackLang.HolProg 64)) :=
  let c := oracleCompilerConfig oracles
  FullMakeInit.fullMakeInit c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    InitECandidate.bitmaps code (labState oracles input t m bitmapDm sharedDm ltconf code)
    (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0
    (fun _ => (ltconf, [], []))

/-- Concrete installation discharges all three initialization obligations:
FullMakeInit's assumptions, its successful optional result, and safe memory.
This is uniform in the input and in any certified source compilation. -/
theorem initialization_exists
    (oracles col : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (code : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config)
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
    FastEnv.baseline_pan_installed_core
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
    (riscvMachineConfigOk _ baseline_machine_isRiscv)
    (oracleMachineInitOk oracles _ baseline_machine_isRiscv) (by decide)
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
    intro a ha
    change (_ && holByteAligned a) = true at ha
    simp only [Bool.and_eq_true] at ha
    exact ha.2

set_option pp.fullNames true
end InitECandidate.Solver.Wave8Stage.ConcreteInitialization
