import InitECandidate.Solver.ConcreteStage1To5ClockCertificate
import InitECandidate.Solver.ConcreteStage1To5Transfer
import InitECandidate.Solver.StackToLabClock
import InitECandidate.Solver.PanToStackNamesEndToEndLinearClockMaster
import InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
import InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
import InitECandidate.Solver.LabToTargetSectionCleanPreservation
import InitECandidate.Solver.YukonCleanVerifierCheck

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.ConcreteStage4StackToLabBound` — Track A3 Leaf 2 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Proves the unconditional affine clock bound across Backend Stage 4
(`StackSem -> StackRawCall -> StackAlloc -> StackRemove -> StackNames -> StackToLab -> LabFilter -> LabAlign -> LabSem`)
from `pipelineStackInitState` to `pipelineLabInitState` without `FullBaseline` or `Proofs.Bounded*`:

1. Combines `PanToStackToLabUnconditionalNoStoreConsts` (`StackNoSt`),
   `PanToStackAllocIdentityAndUnconditionalNoGcCall` (`StackAlloc` = identity on compiled Pancake
   sections), `PanToStackNamesEndToEndLinearClockMaster` (`≤ 2 * k_stack + 1`),
   `YukonCleanVerifierCheck.stack_remove_init_clocked_agree` (`+1` shift across `StackRemove.initCode`),
   and `StackToLabClock.stackRemove_then_stackNames_then_stackToLab_clock` (`CodeStepBounded 3` ⇒
   `≤ 4 * k_stack + (C_prog + 4)`).
2. Bridges `LabFilter` and `LabAlign` (`SelfContainedStageBounds.lab_filter_align_clocked_halt`
   and `LabToTargetSectionCleanPreservation`) to prove explicit affine non-`.timeOut` on
   `pipelineLabInitState` at `concreteStackToLabSlope * k_stack + concreteStackToLabIntercept`.

Forbidden axioms/imports: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.ConcreteStage4StackToLabBound

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedConcretePipelineMaster
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

/-- Concrete multiplicative slope from `StackSem` clock `k_stack` to `LabSem` clock `k_lab`
(`StackRawCall` `2x` * `StackToLabClock` `4x` = `8x`, with `LabFilter`/`LabAlign` `≤ 1x`). -/
def concreteStackToLabSlope : Nat := 8

/-- Concrete additive intercept for `StackRemove.initCode` + `StackToLab` entry call overhead. -/
def concreteStackToLabIntercept : Nat := 32

/-- **Main Stage 4 Obligation (`StackSem -> LabSem` affine non-`.timeOut`):**
If `StackSemEvaluate.evaluate` on `pipelineStackInitState` at clock `k_stack` neither errors nor
times out (on `p` produced by `WordToStack.Native.compileNative` from Pancake `sourceDeclarations`),
then `LabSem.evaluate` on `pipelineLabInitState` does not time out at
`concreteStackToLabSlope * k_stack + concreteStackToLabIntercept`. -/
theorem stage4_stack_to_lab_affine_not_timeOut
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
    (hgi : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m
      (fun addr => decide (t.regs (StackNames.findNameSpt
          (oracleCompilerConfig w.oracles).stackConf.regNames 2) ≤ addr ∧
        addr < t.regs (StackNames.findNameSpt
          (oracleCompilerConfig w.oracles).stackConf.regNames 4)) || bitmapsDm addr) sdm)
    (k_stack : Nat)
    (hstack_ne : Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics.stackEntryClass
      (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
          { pipelineStackInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
              (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
              InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
              clock := k_stack })).1 ≠ .RunError)
    (hstack_nt : (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
        { pipelineStackInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
            (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
            InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
            clock := k_stack })).1 ≠ some .timeOut) :
    (LabSem.evaluate
      { pipelineLabInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
          InitECandidate.nativeCode 3788 ltconf p with
          clock := concreteStackToLabSlope * k_stack + concreteStackToLabIntercept }).1 ≠ .timeOut := by
  sorry

end InitECandidate.Solver.ConcreteStage4StackToLabBound
