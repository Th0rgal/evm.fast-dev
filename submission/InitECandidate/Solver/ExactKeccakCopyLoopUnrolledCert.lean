import InitECandidate.Solver.ExactKeccakSixPassReducedCert
import InitECandidate.Solver.RiscvSszFastRejectAndBootCert

set_option autoImplicit false

/-! Exact arithmetic composition. The imported envelopes and copy-loop savings
are candidate costs: no semantic simulation of an unrolled ROM is asserted.
The SSZ count is the imported guarded-bootstrap model, not an instruction trace.
Certificate bridges below retain compilation and uniform non-timeout obligations
for the baseline ROM explicitly; arithmetic savings alone do not discharge them. -/
namespace InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert

open InitE Flapjack
open InitECandidate.Solver
open ExactKeccakSixPassReducedCert RiscvSszFastRejectAndBootCert
open SelfContainedBoundedCertificate
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

def exactKeccak0UnrolledK : Nat := exactKeccakNoGcK - copyLoopSavedSteps
def exactKeccak128UnrolledK : Nat := exactKeccak128NoGcK - copyLoopSavedSteps

theorem copy_loop_saved_exact : copyLoopSavedSteps = 13_800 :=
  (six_pass_unrolled_copyloop_budget_exact 1 (by decide)).2.2.1

theorem exact_keccak_0_unrolled_exact : exactKeccak0UnrolledK = 2_038_701_869 := by
  simp only [exactKeccak0UnrolledK, no_gc_budget_exact, copy_loop_saved_exact]

theorem exact_keccak_128_unrolled_exact : exactKeccak128UnrolledK = 1_212_035_192 := by
  simp only [exactKeccak128UnrolledK, no_gc_128_budget_exact, copy_loop_saved_exact]

theorem exact_keccak_0_conservation :
    exactKeccak0UnrolledK + copyLoopSavedSteps = exactKeccakNoGcK := by
  rw [exact_keccak_0_unrolled_exact, copy_loop_saved_exact, no_gc_budget_exact]

theorem exact_keccak_128_conservation :
    exactKeccak128UnrolledK + copyLoopSavedSteps = exactKeccak128NoGcK := by
  rw [exact_keccak_128_unrolled_exact, copy_loop_saved_exact, no_gc_128_budget_exact]

theorem exact_keccak_0_saving_exact :
    exactKeccakNoGcK - exactKeccak0UnrolledK = 13_800 := by
  rw [no_gc_budget_exact, exact_keccak_0_unrolled_exact]

theorem exact_keccak_128_saving_exact :
    exactKeccak128NoGcK - exactKeccak128UnrolledK = 13_800 := by
  rw [no_gc_128_budget_exact, exact_keccak_128_unrolled_exact]

theorem exact_keccak_0_one_tick_tight (k : Nat) :
    exactKeccakNoGcK ≤ k + copyLoopSavedSteps ↔ exactKeccak0UnrolledK ≤ k := by
  rw [no_gc_budget_exact, copy_loop_saved_exact, exact_keccak_0_unrolled_exact]
  omega

theorem exact_keccak_128_one_tick_tight (k : Nat) :
    exactKeccak128NoGcK ≤ k + copyLoopSavedSteps ↔ exactKeccak128UnrolledK ≤ k := by
  rw [no_gc_128_budget_exact, copy_loop_saved_exact, exact_keccak_128_unrolled_exact]
  omega

theorem exact_keccak_variants_gap :
    exactKeccak0UnrolledK - exactKeccak128UnrolledK = 826_666_677 := by
  rw [exact_keccak_0_unrolled_exact, exact_keccak_128_unrolled_exact]

theorem exact_keccak_0_yukon_gain (minutes : Nat) :
    yukonScore exactKeccakNoGcK minutes - yukonScore exactKeccak0UnrolledK minutes =
      138_000_000 := by
  unfold yukonScore
  rw [no_gc_budget_exact, exact_keccak_0_unrolled_exact]
  omega

theorem exact_keccak_128_yukon_gain (minutes : Nat) :
    yukonScore exactKeccak128NoGcK minutes - yukonScore exactKeccak128UnrolledK minutes =
      138_000_000 := by
  unfold yukonScore
  rw [no_gc_128_budget_exact, exact_keccak_128_unrolled_exact]
  omega

theorem exact_keccak_yukon_signed_delta (minutes : Nat) :
    (yukonScore exactKeccak0UnrolledK minutes : Int) -
        (yukonScore exactKeccakNoGcK minutes : Int) = -138_000_000 ∧
    (yukonScore exactKeccak128UnrolledK minutes : Int) -
        (yukonScore exactKeccak128NoGcK minutes : Int) = -138_000_000 := by
  unfold yukonScore
  rw [no_gc_budget_exact, no_gc_128_budget_exact,
    exact_keccak_0_unrolled_exact, exact_keccak_128_unrolled_exact]
  omega

theorem ssz_reject_model_exact (loopSteps : Nat) :
    sszGuardedBootstrapSteps false loopSteps = 22 ∧
    sszGuardedBootstrapSteps true loopSteps = 22 + loopSteps := by
  constructor <;> rfl

theorem ssz_reject_model_one_tick_tight (k loopSteps : Nat) :
    sszGuardedBootstrapSteps false loopSteps ≤ k ↔ 22 ≤ k := by
  rw [(ssz_reject_model_exact loopSteps).1]

theorem ssz_header_rejection_characterization (totalLen o0 o1 o2 o3 : Nat) :
    ¬ ValidSszContainerHeader totalLen o0 o1 o2 o3 ↔
      totalLen < 16 ∨ o0 ≠ 16 ∨ o1 < o0 ∨ o2 < o1 ∨ o3 < o2 ∨ totalLen < o3 :=
  (ssz_header_fast_reject_iff_and_examples totalLen o0 o1 o2 o3).1

/-- Conditional baseline certificate at the candidate budget. -/
theorem exact_keccak_0_unrolled_certificate
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
        exactKeccak0UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccak0UnrolledK) (.finite exactKeccak0UnrolledK) := by
  have hsum : bootstrapSteps + (exactKeccak0UnrolledK - bootstrapSteps) = exactKeccak0UnrolledK := by
    rw [InitE.bootstrapSteps_eq, exact_keccak_0_unrolled_exact]
  have hcert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (exactKeccak0UnrolledK - bootstrapSteps) hlab compiled depthBound
    (by simpa only [hsum] using not_timeOut)
  simpa only [hsum] using hcert

/-- Conditional baseline certificate at the candidate budget. -/
theorem exact_keccak_128_unrolled_certificate
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
        exactKeccak128UnrolledK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK exactKeccak128UnrolledK) (.finite exactKeccak128UnrolledK) := by
  have hsum : bootstrapSteps + (exactKeccak128UnrolledK - bootstrapSteps) = exactKeccak128UnrolledK := by
    rw [InitE.bootstrapSteps_eq, exact_keccak_128_unrolled_exact]
  have hcert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (exactKeccak128UnrolledK - bootstrapSteps) hlab compiled depthBound
    (by simpa only [hsum] using not_timeOut)
  simpa only [hsum] using hcert

#print axioms copy_loop_saved_exact
#print axioms exact_keccak_0_unrolled_exact
#print axioms exact_keccak_128_unrolled_exact
#print axioms exact_keccak_0_conservation
#print axioms exact_keccak_128_conservation
#print axioms exact_keccak_0_saving_exact
#print axioms exact_keccak_128_saving_exact
#print axioms exact_keccak_0_one_tick_tight
#print axioms exact_keccak_128_one_tick_tight
#print axioms exact_keccak_variants_gap
#print axioms exact_keccak_0_yukon_gain
#print axioms exact_keccak_128_yukon_gain
#print axioms exact_keccak_yukon_signed_delta
#print axioms ssz_reject_model_exact
#print axioms ssz_reject_model_one_tick_tight
#print axioms ssz_header_rejection_characterization
#print axioms exact_keccak_0_unrolled_certificate
#print axioms exact_keccak_128_unrolled_certificate

end InitECandidate.Solver.ExactKeccakCopyLoopUnrolledCert
