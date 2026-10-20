import InitECandidate.Solver.SelfContainedExactKeccakMasterK
import InitECandidate.Solver.SelfContainedSixPassMaster
import InitECandidate.Solver.WordPassesPreserveNoStoreConsts

set_option autoImplicit false

/-!
Arithmetic composition of the imported extracted Keccak envelopes with the
six-pass slope. The supplied source module has clocks 679564179 and 404008620,
NOT the advertised 5465323432 and 3232111533. These envelopes are not yet
PanSem execution bounds. NoSt is proved for LoopToWord and the tail fragment;
a semantic StackRemove simulation with zero allowance is still required.

The no-GC budget below has zero offsets and no target expansion. It is an
arithmetic candidate, not an unconditional guest bound. Certificate bridges
retain compilation and uniform target non-timeout obligations explicitly.
-/
namespace InitECandidate.Solver.ExactKeccakSixPassReducedCert

open InitE Flapjack
open InitECandidate.Solver
open SelfContainedExactKeccakMasterK
open SelfContainedSixPassMaster
open SelfContainedBoundedCertificate
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Candidate with neutral StackRemove, zero offsets and target expansion one. -/
def exactKeccakNoGcK : Nat := 23_132 + 3 * exactKeccakSourceClock
def exactKeccak128NoGcK : Nat := 23_132 + 3 * exactKeccak128SourceClock

theorem source_clock_exact : exactKeccakSourceClock = 679_564_179 :=
  exact_source_clock_eq

theorem source_128_clock_exact : exactKeccak128SourceClock = 404_008_620 :=
  exact_128_source_clock_eq

/-- The supplied module refutes the task's first claimed source clock. -/
theorem advertised_source_clock_mismatch :
    exactKeccakSourceClock ≠ 5_465_323_432 := by
  rw [source_clock_exact]; decide

theorem advertised_128_source_clock_mismatch :
    exactKeccak128SourceClock ≠ 3_232_111_533 := by
  rw [source_128_clock_exact]; decide

theorem reduced_slope_exact : sixPassSlope 1 3 = 3 :=
  six_pass_slope_three 1 3 rfl rfl

theorem reduced_affine_exact (k : Nat) : sixPassAffine 0 0 0 k = 3 * k := by
  simpa using six_pass_affine_exact 0 0 0 k

theorem no_gc_budget_exact : exactKeccakNoGcK = 2_038_715_669 := by
  unfold exactKeccakNoGcK; rw [source_clock_exact]

theorem no_gc_128_budget_exact : exactKeccak128NoGcK = 1_212_048_992 := by
  unfold exactKeccak128NoGcK; rw [source_128_clock_exact]

theorem no_gc_budget_decomposition :
    exactKeccakNoGcK = bootstrapSteps + sixPassAffine 0 0 0 exactKeccakSourceClock := by
  rw [reduced_affine_exact, bootstrapSteps_eq]; rfl

theorem no_gc_128_budget_decomposition :
    exactKeccak128NoGcK = bootstrapSteps + sixPassAffine 0 0 0 exactKeccak128SourceClock := by
  rw [reduced_affine_exact, bootstrapSteps_eq]; rfl

theorem no_gc_budget_one_tick_tight :
    ¬ bootstrapSteps + 3 * exactKeccakSourceClock ≤ exactKeccakNoGcK - 1 := by
  rw [bootstrapSteps_eq, source_clock_exact, no_gc_budget_exact]; decide

theorem no_gc_128_budget_one_tick_tight :
    ¬ bootstrapSteps + 3 * exactKeccak128SourceClock ≤ exactKeccak128NoGcK - 1 := by
  rw [bootstrapSteps_eq, source_128_clock_exact, no_gc_128_budget_exact]; decide

theorem no_gc_128_below_ten_billion : exactKeccak128NoGcK < 10_000_000_000 := by
  rw [no_gc_128_budget_exact]; decide

theorem no_gc_128_92x_margin : 92 * exactKeccak128NoGcK < 900_719_925_474 := by
  rw [no_gc_128_budget_exact]; decide

theorem no_gc_below_ceiling : exactKeccakNoGcK < 900_719_925_474 := by
  rw [no_gc_budget_exact]; decide

theorem no_gc_128_improves : exactKeccak128NoGcK < exactKeccakNoGcK := by
  rw [no_gc_128_budget_exact, no_gc_budget_exact]; decide

/-- Concrete syntax theorem; no semantic clock claim is inferred from it. -/
theorem loop_to_word_tail_no_store_consts {width : Nat} [NeZero width]
    (ctx : Spt Nat) (p : HolLoopProg width) (l : Nat × Nat) (b : Bool) :
    WordPassesPreserveNoStoreConsts.NoSt
      (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
        (WordInst.threeToTwoRegProg b (LoopToWord.compHOL ctx p l).1))) = true :=
  WordPassesPreserveNoStoreConsts.t_tail_chain b _
    (WordPassesPreserveNoStoreConsts.loopToWord_NoSt ctx p l)

/-- The trace model's zero allowance requires its own no-store trace hypothesis. -/
theorem no_store_trace_allowance (xs : List (Bool × Nat))
    (h : ∀ p ∈ xs, p.1 = false) : StackRemoveClockOriginAudit.runAllowance xs = 0 :=
  stack_remove_no_copy_allowance xs h

/-- Conditional certificate: the target non-timeout obligation remains open. -/
theorem exact_keccak_no_gc_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        exactKeccakNoGcK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccakNoGcK) (.finite exactKeccakNoGcK) :=
  finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (3 * exactKeccakSourceClock) hlab compiled depthBound not_timeOut

/-- Conditional certificate: the target non-timeout obligation remains open. -/
theorem exact_keccak_128_no_gc_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        exactKeccak128NoGcK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccak128NoGcK) (.finite exactKeccak128NoGcK) :=
  finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (3 * exactKeccak128SourceClock) hlab compiled depthBound not_timeOut


#print axioms source_clock_exact
#print axioms source_128_clock_exact
#print axioms advertised_source_clock_mismatch
#print axioms advertised_128_source_clock_mismatch
#print axioms reduced_slope_exact
#print axioms reduced_affine_exact
#print axioms no_gc_budget_exact
#print axioms no_gc_128_budget_exact
#print axioms no_gc_budget_decomposition
#print axioms no_gc_128_budget_decomposition
#print axioms no_gc_budget_one_tick_tight
#print axioms no_gc_128_budget_one_tick_tight
#print axioms no_gc_128_below_ten_billion
#print axioms no_gc_128_92x_margin
#print axioms no_gc_below_ceiling
#print axioms no_gc_128_improves
#print axioms loop_to_word_tail_no_store_consts
#print axioms no_store_trace_allowance
#print axioms exact_keccak_no_gc_certificate
#print axioms exact_keccak_128_no_gc_certificate

end InitECandidate.Solver.ExactKeccakSixPassReducedCert
