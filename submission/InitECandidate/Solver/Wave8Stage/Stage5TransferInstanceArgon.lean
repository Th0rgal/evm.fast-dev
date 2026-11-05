import InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
import InitECandidate.Solver.Wave8Stage.CrepListBudget448
import InitECandidate.Solver.Wave8GuestInv.Certificate

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
open Classical InitE
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.SelfContainedPipelineBridge

theorem stageTransfer_from_witness_and_backend
    (k_pan : Nat)
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (h_word_all : ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true)
    (h_m7313 : ∀ col wprog wconf fs p,
      WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog) →
      WordToStack.Native.compileNative riscvConfig false wprog =
        (InitECandidate.bitmaps, wconf, fs, p) →
      Stage4.codeStepBudget (FullMakeInitSemantics.code2
        (oracleCompilerConfig w.oracles).stackConf (oracleCompilerConfig w.oracles).dataConf
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p) ≤ 7313) :
    UniformSourceClock.CoveredSourceUniformNotTimeOut k_pan →
    FiniteRebudget.UniformNotTimeOut ArtifactEnv.baselineSubmission (118223496 * k_pan + 119233963) :=
  stageTransfer_from_obligations k_pan w CrepListBudget448.crep_listBudget_le_448 h_word_all h_m7313

theorem certificateStageTransfer_from_witness_and_backend
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (h_word_all : ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true)
    (h_m7313 : ∀ col wprog wconf fs p,
      WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog) →
      WordToStack.Native.compileNative riscvConfig false wprog =
        (InitECandidate.bitmaps, wconf, fs, p) →
      Stage4.codeStepBudget (FullMakeInitSemantics.code2
        (oracleCompilerConfig w.oracles).stackConf (oracleCompilerConfig w.oracles).dataConf
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p) ≤ 7313) :
    Wave8GuestInv.StageTransfer :=
  stageTransfer_from_witness_and_backend Wave8GuestInv.K_pan w h_word_all h_m7313

end InitECandidate.Solver.Wave8Stage.Stage5BridgeArgon
