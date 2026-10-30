import InitECandidate.Solver.ConcreteStage1To5ClockCertificate
import InitECandidate.Solver.ConcreteStage1To5Transfer
import InitECandidate.Solver.PanToCrepExactClockIso
import InitECandidate.Solver.WordToStackClockExactOffset
import InitECandidate.Solver.WordToStackSemanticMmioBound
import InitECandidate.Solver.SelfContainedStageBounds

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.ConcreteStage1To3ClockBounds` — Track A3 Leaf 1 (`< 350` LOC)

Frozen Spec Contract (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`):
Proves unconditional affine clock bounds across Frontend Stages 1–3 (`PanSem -> WordSem -> StackSem`)
on the concrete pipeline initial states `pipelinePanToWordInitState` and `pipelineStackInitState`
without `FullBaseline` or `Proofs.Bounded*` imports:

1. **Stage 1–2 (`PanSem -> WordSem`, `CrepToLoop` + `LoopToWord` + `WordToWord`):**
   Closes the existential `∃ k'` in `SelfContainedStageBounds.pan_to_word_clocked_sim` /
   `crepToLoop_ncompile_correct` (`crepToLoopCodeRelEvaluateCallCorrect`), proving an explicit
   affine upper bound `k_word ≤ C_front * k_pan + D_front` so that `PanSem` non-`.timeOut` at
   `k_pan` implies `WordSem` non-`.timeOut` at `C_front * k_pan + D_front` on
   `pipelinePanToWordInitState`.
2. **Stage 3 (`WordSem -> StackSem`, `WordToStack`):**
   Closes the existential `∃ ck` in `SelfContainedStageBounds.word_to_stack_compile_clocked_sim` /
   `WordToStackClockExactOffset.word_to_stack_exact_offset` (where every extra tick in `WordToStack`
   comes from an executed `.raise` or `.shMemOp` consuming at least 1 `WordSem` tick, giving
   `ck ≤ k_word`, i.e., `k_stack ≤ 2 * k_word`, or `k_stack ≤ k_word + D_ws`), proving `StackSem`
   non-`.timeOut` on `pipelineStackInitState`.

Forbidden axioms/imports: NO `sorry`, `axiom`, `native_decide`, `bv_decide`, `Lean.ofReduceBool`,
`InitECandidate.Proofs.Bounded*`, `InitECandidate.Proofs.FullBaseline`, or `Guest.Ast`.
-/

namespace InitECandidate.Solver.ConcreteStage1To3ClockBounds

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
open Flapjack.Compiler.Backend.StackLang

/-- Concrete frontend multiplicative slope (`PanSem -> WordSem`). Workers may tighten or instantiate
this constant (e.g. `2` or explicit AST structural bound on `CrepToLoop` loop/call ticks) provided
`stage1_to_2_pan_to_word_affine_not_timeOut` and `stage1_to_3_word_to_stack_affine_not_timeOut`
compile with zero hypotheses and `C_front ≥ 1`. -/
def concreteFrontSlope : Nat := 2

/-- Concrete frontend additive intercept (`globalsInit` + `main` wrapper entry ticks). -/
def concreteFrontIntercept : Nat := 16

/-- Concrete `WordToStack` multiplicative slope (`ck ≤ k_word` ⇒ `k_stack ≤ 2 * k_word`). -/
def concreteWordToStackSlope : Nat := 2

/-- **Obligation 1 (`PanSem -> WordSem` affine non-`.timeOut`):**
If `PanSem` does not time out at `k_pan` from `s_decls` on a covered terminating input, then
`WordSemStateFiniteExact.evaluate` on `pipelinePanToWordInitState` does not time out at
`concreteFrontSlope * k_pan + concreteFrontIntercept`. -/
theorem stage1_to_2_pan_to_word_affine_not_timeOut
    (w : ConcreteOracleCompilationWitness)
    (input : Guest.InputBlob)
    (hgas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hsource : sourceBehaviour input = .terminate outcome events)
    (hcov : coveredOutcome outcome)
    (k_pan : Nat)
    (hpan_nt : ∀ (stCtxt : StructContextExact)
        (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
      decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls →
      (PanSemStateFiniteExact.evaluateHOLFiniteState
        { s_decls with clock := k_pan }
        (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config)
    (hinst : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m
      (fun addr => decide (t.regs (StackNames.findNameSpt
          (oracleCompilerConfig w.oracles).stackConf.regNames 2) ≤ addr ∧
        addr < t.regs (StackNames.findNameSpt
          (oracleCompilerConfig w.oracles).stackConf.regNames 4)) || bitmapsDm addr) sdm) :
    (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelinePanToWordInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
          (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
          InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
          InitECandidate.bitmaps p 0 with
          clock := concreteFrontSlope * k_pan + concreteFrontIntercept }).1 ≠ some .timeOut := by
  sorry

/-- **Obligation 2 (`WordSem -> StackSem` affine non-`.timeOut`):**
If `WordSem` on `pipelineWordInitState` (post-`WordToWord`, which agrees 1:1 in clock with
`pipelinePanToWordInitState` via `SelfContainedStageBounds.word_to_word_clocked_agree`) does not
time out at `k_word` and does not error, then `StackSemEvaluate.evaluate` on `pipelineStackInitState`
does not time out at `concreteWordToStackSlope * k_word`. -/
theorem stage2_to_3_word_to_stack_affine_not_timeOut
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
            clock := concreteWordToStackSlope * k_word })).1 ≠ some .timeOut := by
  sorry

end InitECandidate.Solver.ConcreteStage1To3ClockBounds
