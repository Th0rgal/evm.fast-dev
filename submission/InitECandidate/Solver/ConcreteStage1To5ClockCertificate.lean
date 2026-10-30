import InitECandidate.Solver.SelfContainedConcretePipelineMaster
import InitECandidate.Solver.SelfContainedBasicBlockBridge
import InitECandidate.Solver.StackToLabClock
import InitECandidate.Solver.GuestGasAndSpecFixes
import InitECandidate.Solver.WordToStackSemanticMmioBound
import InitECandidate.Solver.PanToStackNamesEndToEndLinearClockMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# Concrete Stage 1–5 clock certificate

This leaf module imports only `Solver/` modules whose transitive closure is
free of `InitECandidate.Proofs.FullBaseline` and `InitECandidate.Proofs.Bounded*`.

It does three things:

1.  It instantiates the `ConcreteOracleCompilationWitness` of
    `SelfContainedConcretePipelineMaster` with the concrete
    `baselineConfigLiteral` compiler configuration.  The single remaining
    premise is the *artifact* compiler-computation equality
    `compileProgMaxAsmExecutable … = (some …, some depth)`.
2.  It records the clock-monotonicity transfer lemmas that move non-`.timeOut`
    runs to any larger budget (`WordSem`, `StackSem`, `LabSem`, and the RISC-V
    target), so that the per-stage simulation clocks can be replaced by any
    affine upper bound on them.
3.  It re-exports, at concrete numeric slopes, the Stage 1–5 quantitative clock
    bounds already proved in the `Solver/` graph, and packages the resulting
    `InitE.Certificate (baselineWithFiniteK K) (.finite K)` for the three
    concrete `PanSem` gas budgets (coarse, Farkas-patched and refined
    `keccak256`).
-/

namespace InitECandidate.Solver.ConcreteStage1To5ClockCertificate

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedConcretePipelineMaster
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

/-- The concrete compiler configuration used by the submission satisfies the
`LabToTarget.Config` side condition of the oracle compilation witness. -/
theorem baselineConfigLiteral_labConf :
    baselineConfigLiteral.labConf = baselineLabConfig := rfl

/-- Every `ConcreteOracleCompilationWitness` has `LabToTarget.Config` equal to
the concrete `baselineLabConfig`. -/
theorem witness_labConf_eq (w : ConcreteOracleCompilationWitness) :
    w.c.labConf = baselineLabConfig := w.hlab

/-- A single `compileProgMaxAsmExecutable` artifact computation for the concrete
`baselineConfigLiteral` inhabits the otherwise `FullBaseline`-free
`ConcreteOracleCompilationWitness`. -/
def concreteOracleCompilationWitness
    (oracles : List (Option (Spt Nat))) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations =
        (some (InitECandidate.nativeCode, InitECandidate.bitmaps, baselineConfigLiteral),
          some depth))
    (depthBound : depth ≤ 7480) :
    ConcreteOracleCompilationWitness :=
  ⟨oracles, baselineConfigLiteral, depth, baselineConfigLiteral_labConf, compiled, depthBound⟩

/-! ## 1. Clock monotonicity: non-`.timeOut` runs survive larger budgets -/

/-- `WordSem`: if a run at clock `k` does not time out, the run at `k + extra`
has the same result and therefore still does not time out. -/
theorem word_evaluate_add_clock {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (hnt : (WordSemStateFiniteExact.evaluate p s).1 ≠ some WordSemResult.timeOut) :
    (WordSemStateFiniteExact.evaluate p
      { s with clock := s.clock + extra }).1 ≠ some WordSemResult.timeOut := by
  rcases hr : WordSemStateFiniteExact.evaluate p s with ⟨r, s'⟩
  have h := WordSemStateFiniteExact.evaluate_add_clock extra p s r s'
    ⟨hr, by rw [hr] at hnt; exact hnt⟩
  rw [h]
  rw [hr] at hnt
  exact hnt

/-- `StackSem`: the same monotonicity statement. -/
theorem stack_evaluate_add_clock {width : Nat} [NeZero width] {C F : Type}
    (extra : Nat) (p : StackLang.HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (hnt : (StackSemEvaluate.evaluate (p, s)).1 ≠ some StackSemResult.timeOut) :
    (StackSemEvaluate.evaluate (p,
      { s with clock := s.clock + extra })).1 ≠ some StackSemResult.timeOut := by
  rcases hr : StackSemEvaluate.evaluate (p, s) with ⟨r, s'⟩
  have h := StackProps.evaluateAddClock extra p s r s'
    ⟨hr, by rw [hr] at hnt; exact hnt⟩
  rw [h]
  rw [hr] at hnt
  exact hnt

/-- `LabSem`: the same monotonicity statement. -/
theorem lab_evaluate_add_clock {width : Nat} [NeZero width] {C F : Type}
    (s : LabSem.State width C F) (extra : Nat)
    (hnt : (LabSem.evaluate s).1 ≠ MachineResult.timeOut) :
    (LabSem.evaluate { s with clock := s.clock + extra }).1 ≠ MachineResult.timeOut := by
  rcases hr : LabSem.evaluate s with ⟨r, s'⟩
  have h := LabProps.evaluateAddClock s r s' extra
    ⟨hr, by rw [hr] at hnt; exact hnt⟩
  rw [h]
  rw [hr] at hnt
  exact hnt

/-- RISC-V target: `SelfContainedBasicBlockBridge.evaluateTarget_add_clock_of_not_timeOut`. -/
theorem target_evaluate_add_clock :
    type_of% @SelfContainedBasicBlockBridge.evaluateTarget_add_clock_of_not_timeOut :=
  @SelfContainedBasicBlockBridge.evaluateTarget_add_clock_of_not_timeOut

/-- Any non-`.timeOut` run at `k` transfers to every `k' ≥ k`. -/
theorem target_not_timeOut_mono {S Q σ : Type}
    (mc : MachineConfig 64 S Q) (ffi : HolFfiState σ) (ms : S) (k k' : Nat)
    (hk : k ≤ k')
    (hnt : (evaluateTargetHOL mc ffi k ms).1 ≠ MachineResult.timeOut) :
    (evaluateTargetHOL mc ffi k' ms).1 ≠ MachineResult.timeOut := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact (SelfContainedBasicBlockBridge.evaluateTarget_add_clock_of_not_timeOut
    mc ffi ms k d hnt).2

/-! ## 2. Concrete quantitative per-stage clock bounds -/

/-- Stage 1a (`PanToCrep`): exact `1:1` entry-clock isometry. -/
theorem stage1a_pan_to_crep_clock_iso :
    type_of% @PanToCrepExactClockIso.pan_to_crep_full_entry_clock_iso :=
  @PanToCrepExactClockIso.pan_to_crep_full_entry_clock_iso

/-- Stage 1b (`CrepToLoop` + `LoopToWord`) into `WordSem`. -/
theorem stage1_pan_to_word_clocked_sim :
    type_of% @SelfContainedStageBounds.pan_to_word_clocked_sim :=
  @SelfContainedStageBounds.pan_to_word_clocked_sim

/-- Stage 1c (`WordToWord`): same-clock non-`.timeOut` agreement. -/
theorem stage1_word_to_word_clocked_agree :
    type_of% @SelfContainedStageBounds.word_to_word_clocked_agree :=
  @SelfContainedStageBounds.word_to_word_clocked_agree

/-- Stage 2 (`WordToStack`) simulation clock offset `ck`. -/
theorem stage2_word_to_stack_clocked_sim_exact_offset :
    type_of% @SelfContainedStageBounds.word_to_stack_clocked_sim :=
  @SelfContainedStageBounds.word_to_stack_clocked_sim

/-- Stage 2 quantitative offset decomposition `ck ≤ raises + shares`. -/
theorem stage2_word_to_stack_ticks_decomp :
    type_of% @WordToStackSemanticMmioBound.word_to_stack_ticks_decomp :=
  @WordToStackSemanticMmioBound.word_to_stack_ticks_decomp

/-- Stage 3 (`StackRawCall` → `StackAlloc` → `StackRemove` → `StackNames`):
end-to-end linear clock bound `≤ 2 * k_stack + 1`. -/
theorem stage3_pancake_to_stackNames_end_to_end_linear_clock :
    type_of% @PanToStackNamesEndToEndLinearClockMaster.pancake_to_stackNames_end_to_end_linear_clock :=
  @PanToStackNamesEndToEndLinearClockMaster.pancake_to_stackNames_end_to_end_linear_clock

/-- Stage 4 (`StackRemove` + `StackNames` + `StackToLab`): with
`CodeStepBounded M`, `C_prog ≤ M`, and `M ≤ 3`, the `LabSem` run finishes within
`4 * k_stack + (C_prog + 4)` ticks. -/
theorem stage4_stackRemove_stackNames_stackToLab_clock :
    type_of% @StackToLabClock.stackRemove_stackNames_stackToLab_clock :=
  @StackToLabClock.stackRemove_stackNames_stackToLab_clock

/-- Stage 4 entry `LabFilter`/`LabAlign` clocked halt. -/
theorem stage4_lab_filter_align_clocked_halt :
    type_of% @SelfContainedStageBounds.lab_filter_align_clocked_halt :=
  @SelfContainedStageBounds.lab_filter_align_clocked_halt

/-- Maximum RISC-V machine instructions emitted per standard `LabLang` line (`maxEncSteps = 4`). -/
def maxEncSteps : Nat := 4

/-- Stage 5 (`LabToTarget`) multi-step clock bound (`SelfContainedBasicBlockBridge.lab_to_target_multi_step_clock_bound`). -/
theorem stage5_labToTarget_bounded_step_simulation :
    type_of% @SelfContainedBasicBlockBridge.lab_to_target_multi_step_clock_bound :=
  @SelfContainedBasicBlockBridge.lab_to_target_multi_step_clock_bound

/-- Stage 5 basic-block multi-step bound. -/
theorem stage5_lab_to_target_basic_block_multi_step_bound :
    type_of% @SelfContainedBasicBlockBridge.lab_to_target_basic_block_multi_step_bound :=
  @SelfContainedBasicBlockBridge.lab_to_target_basic_block_multi_step_bound

/-- The RISC-V encoder emits at most `maxEncSteps = 4` instructions, hence the
per-tick target slope is at most `4`. -/
theorem maxEncSteps_le_four : maxEncSteps ≤ 4 := Nat.le_refl 4

/-! ## 3. Concrete `PanSem` gas budgets and finite baseline certificates -/

/-- Coarse `PanSem` clock bound at a `200M` declared gas limit. -/
def coarsePanClockBound : Nat := Guest.maxInputBytes + 219 * 200000000

/-- Farkas-certified patched `200M`-gas `PanSem` clock bound. -/
def patchedPanClockBound : Nat := GuestGasAndSpecFixes.patchedGuest200MBound

/-- Refined `keccak256` `PanSem` clock bound. -/
def refinedPanClockBound : Nat := SelfContainedMasterK.refinedSourceClock

theorem patchedPanClockBound_value : patchedPanClockBound = 6575582388 := rfl

theorem coarsePanClockBound_value : coarsePanClockBound = 44873741808 := by
  unfold coarsePanClockBound Guest.maxInputBytes
  decide

/-- Concrete Stage 1–5 finite baseline certificate at an arbitrary affine
budget.  `K = bootstrapSteps + linearPipelineTargetBudget K_pan_max C_front
D_front C_back D_back C_target`; the remaining explicit hypotheses are the
uniform `PanSem` non-`.timeOut` premise and the four affine stage-clock bounds.
No `FullBaseline` import is needed. -/
theorem concrete_affine_stage1_to_5_certificate
    (w : ConcreteOracleCompilationWitness)
    (K_pan_max C_front D_front C_back D_back C_target : Nat)
    (k_pan k_word k_stack k_lab : Guest.InputBlob → Nat)
    (h_pan_bound : ∀ input, k_pan input ≤ K_pan_max)
    (h_front_bound : ∀ input, k_word input ≤ C_front * k_pan input + D_front)
    (h_stack_bound : ∀ input, k_stack input ≤ k_word input + D_back)
    (h_back_bound : ∀ input, k_lab input ≤ C_back * k_word input + D_back)
    (pan_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
          decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
            { sourceInitialState input with structs := stCtxt }
            (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
            sourceDeclarations = some s_decls →
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := k_pan input }
            (.call none (Flapjack.Basis.Pure.MlString.ofString "main") [] : ProgHOL 64)).1
              ≠ some .timeOut)
    (stage2_to_5_clock_transfer :
      (∀ (input : Guest.InputBlob),
        Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
        ∀ (outcome : HolOutcome) (events : List HolIoEvent),
          sourceBehaviour input = .terminate outcome events →
          coveredOutcome outcome →
          ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
            decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
            @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
              { sourceInitialState input with structs := stCtxt }
              (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
              sourceDeclarations = some s_decls →
            (PanSemStateFiniteExact.evaluateHOLFiniteState
              { s_decls with clock := k_pan input }
              (.call none (Flapjack.Basis.Pure.MlString.ofString "main") [] : ProgHOL 64)).1
                ≠ some .timeOut) →
      (∀ (input : Guest.InputBlob),
        Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
        ∀ (outcome : HolOutcome) (events : List HolIoEvent),
          sourceBehaviour input = .terminate outcome events →
          coveredOutcome outcome →
          (∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
            (bitmapsDm sdm : BitVec 64 → Bool)
            (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
            (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
            (WordSemStateFiniteExact.evaluate
              (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
              { pipelinePanToWordInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
                  InitECandidate.bitmaps p 0 with clock := k_word input }).1 ≠ some .timeOut) ∧
          (∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
            (bitmapsDm sdm : BitVec 64 → Bool)
            (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
            (StackSemEvaluate.evaluate
              ((.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64),
                { pipelineStackInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
                    (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                    InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
                    clock := k_stack input })).1 ≠ some .timeOut) ∧
          (∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
            (bitmapsDm sdm : BitVec 64 → Bool)
            (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
            (LabSem.evaluate
              { pipelineLabInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf p with
                  clock := k_lab input }).1 ≠ .timeOut) ∧
          (∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
            (bitmapsDm sdm : BitVec 64 → Bool)
            (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
            (LabSem.evaluate
              { pipelineLabInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf p with
                  clock := k_lab input }).1 = .halt outcome →
            (LabSem.evaluate
              { pipelineLabInitState (oracleCompilerConfig w.oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf p with
                  clock := k_lab input }).2.ffi.ioEvents = events →
            (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
              (bootstrapSteps + linearPipelineTargetBudget K_pan_max C_front D_front
                C_back D_back C_target)
              (baselineInitialState input)).1 ≠ .timeOut))) :
    let K := bootstrapSteps +
      linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target
    (∀ input,
      k_stack input ≤ C_front * K_pan_max + D_front + D_back ∧
      C_target * k_lab input ≤
        linearPipelineTargetBudget K_pan_max C_front D_front C_back D_back C_target) ∧
    InitE.Certificate (baselineWithFiniteK K) (.finite K) ∧
    InitE.Certificate SelfContainedEndToEndCert.submission .infinity :=
  concrete_pipeline_certificate_of_uniform_pan_not_timeOut
    w.oracles w.c w.depth K_pan_max C_front D_front C_back D_back C_target
    w.hlab w.compiled w.depthBound k_pan k_word k_stack k_lab
    h_pan_bound h_front_bound h_stack_bound h_back_bound
    pan_not_timeOut stage2_to_5_clock_transfer

/-- Any uniform target non-`.timeOut` at the finite budget `K` immediately
gives the finite baseline certificate and the `.infinity` submission
certificate, with no per-input existential hypotheses. -/
theorem concrete_certificate_of_target_not_timeOut
    (w : ConcreteOracleCompilationWitness) (K : Nat)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K
          (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK K) (.finite K) ∧
    InitE.Certificate SelfContainedEndToEndCert.submission .infinity := by
  have h := certificate_of_target_not_timeOut_of_witness w K not_timeOut
  exact ⟨h, baseline_infinity_certificate_of_finite K h⟩

/-- A uniform target non-`.timeOut` premise at `K` transfers to every larger
budget by `evaluateTarget_add_clock_of_not_timeOut`. -/
theorem concrete_certificate_mono
    (w : ConcreteOracleCompilationWitness) (K K' : Nat) (hK : K ≤ K')
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K
          (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK K') (.finite K') := by
  refine certificate_of_target_not_timeOut_of_witness w K' ?_
  intro input hgas outcome events source covered
  exact target_not_timeOut_mono baselineMachineConfig (sourceFfi input)
    (baselineInitialState input) K K' hK (not_timeOut input hgas outcome events source covered)

end InitECandidate.Solver.ConcreteStage1To5ClockCertificate
