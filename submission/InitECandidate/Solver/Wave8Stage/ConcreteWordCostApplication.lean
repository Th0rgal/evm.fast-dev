import InitECandidate.Solver.Wave8Stage.ConcreteWordCostAnnotations
import InitECandidate.Solver.ConcreteCompilationWitness
import InitECandidate.Solver.PipelineInitialStates

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteWordCostApplication
open InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs
open InitECandidate.Solver.FastEnv InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedConcretePipelineMaster

/-- The exact concrete stage-2 pipeline and clock follow from the remaining
finite guest-prefix checks. Both initialization branches are proved internally;
there is no installation or successful-initialization assumption. This is
conditional on those checks, not a proof of the frozen stage-2 declaration. -/
theorem stage2_to_3_of_checked
    (checked : ∀ entry ∈ panToWordCompileProgHOL riscvConfig.isa sourceDeclarations,
      WordCostCheck.checkProgram ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal 20000
        (WordCostCompilerControl.preAllocation riscvConfig riscvConfig.twoRegArith entry.2.1 entry.2.2)
        (ConcreteWordCostAnnotations.summaries (some entry.1)) = true)
    (w : ConcreteOracleCompilationWitness)
    (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool)
    (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config)
    (hwtw : WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog))
    (hwts : WordToStack.Native.compileNative riscvConfig false wprog =
      (InitECandidate.bitmaps, wconf, fs, p))
    (k_word : Nat)
    (hsafe : WordSemStateFiniteExact.wordLangSafeForSpace
      (pipelineWordInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
        (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
        InitECandidate.nativeCode 3788 ltconf wprog InitECandidate.bitmaps p 0)
      BvlToBvi.initGlobalsLocation)
    (hw_ne : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelineWordInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
          InitECandidate.nativeCode 3788 ltconf wprog InitECandidate.bitmaps p 0 with
          clock := k_word }).1 ≠ some .error)
    (hw_nt : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelineWordInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
          InitECandidate.nativeCode 3788 ltconf wprog InitECandidate.bitmaps p 0 with
          clock := k_word }).1 ≠ some .timeOut) :
    (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
        { pipelineStackInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
            (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
            InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
            clock := 2 * k_word })).1 ≠ some .timeOut := by
  let c := oracleCompilerConfig w.oracles
  let sp := baselineMachineConfig.target.config.regCount -
    (baselineMachineConfig.target.config.avoidRegs.length + 3)
  let maxHeap := 2 * DataToWord.maxHeapLimit 64 c.dataConf - 1
  let lab := pipelineLabInitState c baselineMachineConfig (sourceFfi input) t m bitmapsDm sdm
    baselineInstalledState InitECandidate.nativeCode 3788 ltconf p
  let result := FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
    baselineMachineConfig.target.config.addrOffset InitECandidate.bitmaps p lab
    (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0 (fun _ => (ltconf, [], []))
  exact WordCostFullPipelineCertificate.notTimeOut_two_mul riscvConfig c.wordToWordConf
    sourceDeclarations col wprog InitECandidate.bitmaps wconf fs p c.stackConf c.dataConf
    maxHeap sp baselineMachineConfig.target.config.addrOffset lab
    (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0 ltconf result.1 result.2
    BvlToBvi.initGlobalsLocation k_word ConcreteWordCostAnnotations.summaries WordSourceOracle.terminal
    sourceOracle 20000 ConcreteWordCostAnnotations.noLabels ConcreteWordCostAnnotations.indirect
    checked ConcreteWordCostAnnotations.entryBound rfl WordSourceOracle.terminalOracle
    (.inr rfl) (by decide) ConcreteWordCostAnnotations.bitmapBound ConcreteWordCostAnnotations.bitmapPrefix
    (by decide) (by decide) hwtw hwts rfl hw_ne hw_nt

#print axioms stage2_to_3_of_checked
end InitECandidate.Solver.Wave8Stage.ConcreteWordCostApplication
