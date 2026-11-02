import InitECandidate.Solver.ConcreteStage1To5ClockCertificate
import InitECandidate.Solver.ConcreteStage1To5Transfer
import InitECandidate.Solver.SelfContainedBasicBlockBridge
import InitECandidate.Solver.LoopToWordToStackNamesAndLabToTargetClockMaster
import InitECandidate.Solver.LabToTargetSectionCleanPreservation
import InitECandidate.Solver.YukonBaselineCompat
import InitECandidate.Solver.YukonCleanVerifierCheck

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.ConcreteStage5LabToTargetTransfer` — Track A3 Leaf 3 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Proves the unconditional Stage 5 (`LabSem -> RISC-V Target`) clock transfer from
`pipelineLabInitState` halting at `k_lab` to `evaluateTargetHOL baselineMachineConfig` not timing
out at `bootstrapSteps + concreteTargetSlope * k_lab` on `baselineInitialState input`:

1. Uses `YukonCleanVerifierCheck.oracle_baseline_installation` / `baseline_pan_installed` and
   `BootstrapTrace.full_evaluator_exact` (`bootstrapSteps = 23077`) to step from
   `baselineInitialState input` to the post-bootstrap `baselineInstalledState` related by
   `LabToTarget.stateRel` to `pipelineLabInitState`.
2. Instantiates `LabToTarget.compileCorrect` / `encoderCorrect riscvTarget` per-tick target step
   bounds (`l ≤ riscvMaxBasicBlockExtra + 1 = 9`, or `maxEncSteps = 4` where applicable) with
   `SelfContainedBasicBlockBridge.lab_to_target_multi_step_clock_bound` and
   `ConcreteStage1To5ClockCertificate.target_not_timeOut_mono` to eliminate the existential `∃ k`
   in `LoopToWordToStackNamesAndLabToTargetClockMaster.labToTarget_clock_plus_k`.

Forbidden axioms/imports: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.ConcreteStage5LabToTargetTransfer

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedConcretePipelineMaster
open InitECandidate.Solver.SelfContainedBasicBlockBridge
open InitECandidate.Solver.ConcreteStage1To5ClockCertificate
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackLang

/-- Concrete target instructions per `LabSem` tick (`riscvMaxBasicBlockExtra + 1 = 9`).
Workers may tighten to `4` if proved unconditionally for all reachable `Asm` instructions. -/
def concreteTargetSlope : Nat := 9

/-- **Main Stage 5 Obligation (`LabSem -> Target` concrete non-`.timeOut` transfer):**
Given `w : ConcreteOracleCompilationWitness` and `LabSem.evaluate` halting with `.halt outcome`
and `events` at clock `k_lab` on `pipelineLabInitState` (under the standard installation witnesses
extracted by `SelfContainedConcretePipelineMaster`), `evaluateTargetHOL` on
`baselineInitialState input` does NOT time out at `bootstrapSteps + concreteTargetSlope * (k_lab + 1)`. -/
theorem stage5_lab_to_target_affine_not_timeOut
    (w : ConcreteOracleCompilationWitness)
    (input : Guest.InputBlob)
    (hgas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hsource : sourceBehaviour input = .terminate outcome events)
    (hcov : coveredOutcome outcome)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool)
    (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config)
    (code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (hwtw : WordToWord.compile (oracleCompilerConfig w.oracles).wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa sourceDeclarations) = (col, wprog))
    (hwts : WordToStack.Native.compileNative riscvConfig false wprog =
      (InitECandidate.bitmaps, wconf, fs, p))
    (hltc : LabToTarget.compile riscvConfig ltconf
      (StackToLab.compile (oracleCompilerConfig w.oracles).stackConf
        (oracleCompilerConfig w.oracles).dataConf
        (2 * DataToWord.maxHeapLimit 64 (oracleCompilerConfig w.oracles).dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
        riscvConfig.addrOffset p) = some (InitECandidate.nativeCode,
          { ltconf with labels := labs, asmConf := riscvConfig }))
    (hrel : LabToTarget.stateRel
      (baselineMachineConfig, code2, labs,
        baselineMachineConfig.target.getPc baselineInstalledState +
          BitVec.ofNat 64 InitECandidate.nativeCode.length)
      (pipelineLabInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
        (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
        InitECandidate.nativeCode 3788 ltconf p)
      t baselineInstalledState)
    (htie : LabToTarget.oracleTie baselineMachineConfig baselineInstalledState
      (pipelineLabInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
        (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
        InitECandidate.nativeCode 3788 ltconf p))
    (k_lab : Nat)
    (hlab_halt : (LabSem.evaluate
      { pipelineLabInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
          InitECandidate.nativeCode 3788 ltconf p with
          clock := k_lab }).1 = .halt outcome)
    (hlab_io : (LabSem.evaluate
      { pipelineLabInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
          InitECandidate.nativeCode 3788 ltconf p with
          clock := k_lab }).2.ffi.ioEvents = events) :
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + concreteTargetSlope * (k_lab + 1))
      (baselineInitialState input)).1 ≠ .timeOut := by
  sorry

end InitECandidate.Solver.ConcreteStage5LabToTargetTransfer
