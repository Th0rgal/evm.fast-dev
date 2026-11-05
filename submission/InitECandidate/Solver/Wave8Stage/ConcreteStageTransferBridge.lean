import InitECandidate.Solver.Wave8Stage.Stage5TransferInstanceArgon
import InitECandidate.Solver.Wave8Stage.ConcreteStage2To5Inst
import InitECandidate.Solver.ConcreteCompilationWitness

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteStageTransferBridge
open InitE Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver InitECandidate.Solver.Wave8GuestInv

def compilationWitness
    (w : SelfContainedConcretePipelineMaster.ConcreteOracleCompilationWitness) :
    LeanBridge.ConcreteOracleCompilationWitness :=
  { oracles := w.oracles
    c := w.c
    depth := w.depth
    hlab := w.hlab
    compiled := w.compiled
    depthBound := w.depthBound }

def BackendBound (w : LeanBridge.ConcreteOracleCompilationWitness) : Prop :=
  ∀ col wprog wconf fs p,
    WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog) →
    WordToStack.Native.compileNative riscvConfig false wprog =
      (InitECandidate.bitmaps, wconf, fs, p) →
    Stage4.codeStepBudget (FullMakeInitSemantics.code2
      (oracleCompilerConfig w.oracles).stackConf (oracleCompilerConfig w.oracles).dataConf
      (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset p) ≤ 7313

theorem stageTransfer
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (checked : ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true)
    (backend : BackendBound w) : StageTransfer :=
  Stage5BridgeArgon.certificateStageTransfer_from_witness_and_backend w checked backend

theorem targetClockBound
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (checked : ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true)
    (backend : BackendBound w)
    (source : UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan) : TargetClockBound :=
  stageTransfer w checked backend source

theorem finiteCertificate
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (checked : ConcreteCompilerWord.source.all ConcreteWordCheckInput.check = true)
    (backend : BackendBound w)
    (source : UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan) :
    InitE.Certificate Wave8GuestInv.submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (targetClockBound w checked backend source)

theorem uncertifiedStageTransfer
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (hbound : ∀ col wprog wconf fs p,
      WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog) →
      WordToStack.Native.compileNative riscvConfig false wprog =
        (InitECandidate.bitmaps, wconf, fs, p) →
      ConcreteStage2To5Inst.concreteTargetClock wprog w.oracles p K_pan ≤ K_target) :
    StageTransfer :=
  ConcreteStage2To5Inst.uncertified_uniform_not_timeOut_bounded w K_pan K_target hbound

theorem uncertifiedFiniteCertificate
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (hbound : ∀ col wprog wconf fs p,
      WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog) →
      WordToStack.Native.compileNative riscvConfig false wprog =
        (InitECandidate.bitmaps, wconf, fs, p) →
      ConcreteStage2To5Inst.concreteTargetClock wprog w.oracles p K_pan ≤ K_target)
    (source : UniformSourceClock.CoveredSourceUniformNotTimeOut K_pan) :
    InitE.Certificate Wave8GuestInv.submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (uncertifiedStageTransfer w hbound source)

end InitECandidate.Solver.Wave8Stage.ConcreteStageTransferBridge
