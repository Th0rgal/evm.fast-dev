import InitECandidate.Solver.GuestDirtyWriteHtabDominance
import InitECandidate.Solver.BlockVsTxSixPassTargetCert
import InitECandidate.Solver.SelfContainedSixPassMaster

set_option autoImplicit false

/-! Conditional arithmetic envelopes for the bs32 probe model. The total envelope
adds the named source components; it is not a proved Guest semantic clock bound.
Expansion hypotheses must cover all affine offsets and instruction expansion.
Finite certificates retain compilation and uniform target non-timeout obligations.
One-tick tightness concerns the saturated arithmetic model, not an execution witness. -/
namespace InitECandidate.Solver.Bs32DominanceSixPassTargetCert
open InitE Flapjack
open InitECandidate.Solver
open SelfContainedBoundedCertificate
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

def bs32MaxProbeTicks : Nat := 2 * (47_619 * 1_000_001)
def bs32TotalSourceClock : Nat :=
  95_238_095_238 + 16_777_200_000 + 13_605_272_109 + 3_659_564_234
def bs32StandaloneSourceClock : Nat := 95_238_095_238 + 3_659_564_234
def threePassSlope : Nat := SelfContainedSixPassMaster.sixPassSlope 1 3
def sixPassSlope : Nat := SelfContainedSixPassMaster.sixPassSlope 1 6

theorem three_pass_slope_exact : threePassSlope = 3 :=
  BlockVsTxSixPassTargetCert.slope3_reduction

theorem six_pass_slope_exact : sixPassSlope = 6 :=
  BlockVsTxSixPassTargetCert.slope6_reduction

theorem bs32_max_probe_exact : bs32MaxProbeTicks = 95_238_095_238 := by decide

theorem bs32_probe_bound (D W : Nat)
    (h : GuestDirtyWriteHtabDominance.noopColdUnits * D + W ≤ 2_000_000) :
    2 * (D * W) ≤ bs32MaxProbeTicks :=
  GuestDirtyWriteHtabDominance.bs32_term_le D W h

theorem bs32_probe_attained :
    GuestDirtyWriteHtabDominance.noopColdUnits * 47_619 + 1_000_001 = 2_000_000 ∧
    GuestDirtyWriteHtabDominance.pBs32 * (47_619 * 1_000_001) = bs32MaxProbeTicks :=
  GuestDirtyWriteHtabDominance.bs32_term_tight

theorem bs32_probe_one_tick_tight :
    ¬ 2 * (47_619 * 1_000_001) ≤ bs32MaxProbeTicks - 1 := by decide

theorem bs32_total_source_exact : bs32TotalSourceClock = 129_280_131_581 := by decide

theorem bs32_standalone_source_exact : bs32StandaloneSourceClock = 98_897_659_472 := by decide

theorem bs32_total_decomposition :
    bs32TotalSourceClock = bs32MaxProbeTicks + 16_777_200_000 +
      13_605_272_109 + 3_659_564_234 := by decide

theorem bs32_standalone_decomposition :
    bs32StandaloneSourceClock = bs32MaxProbeTicks + 3_659_564_234 := by decide

theorem block_read_component :
    GuestBlockVsTxHtabBounds.blkRead GuestBlockVsTxHtabBounds.maxColdPerBlock =
      13_605_272_109 := BlockVsTxSixPassTargetCert.block_read_exact

theorem linear_component :
    SelfContainedMasterK.prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap =
      3_659_564_234 := BlockVsTxSixPassTargetCert.push31_linear_exact

theorem bs32_standalone_source_bound (D W : Nat)
    (h : GuestDirtyWriteHtabDominance.noopColdUnits * D + W ≤ 2_000_000) :
    2 * (D * W) + 3_659_564_234 ≤ bs32StandaloneSourceClock := by
  have hp := bs32_probe_bound D W h
  rw [bs32_standalone_decomposition]
  omega

theorem bs32_total_source_bound (D W : Nat)
    (h : GuestDirtyWriteHtabDominance.noopColdUnits * D + W ≤ 2_000_000) :
    2 * (D * W) + 16_777_200_000 + 13_605_272_109 + 3_659_564_234 ≤
      bs32TotalSourceClock := by
  have hp := bs32_probe_bound D W h
  rw [bs32_total_decomposition]
  omega

def bs32StandaloneSlope3K : Nat := 23_132 + 3 * bs32StandaloneSourceClock
def bs32_standalone_slope3_postSteps : Nat := 3 * bs32StandaloneSourceClock

theorem bs32_standalone_slope3_exact : bs32StandaloneSlope3K = 296_693_001_548 := by decide

theorem bs32_standalone_slope3_decomposition :
    bs32StandaloneSlope3K = bootstrapSteps + bs32_standalone_slope3_postSteps := by
  rw [bootstrapSteps_eq]; rfl

theorem bs32_standalone_slope3_slope_formula :
    bs32StandaloneSlope3K = bootstrapSteps + threePassSlope * bs32StandaloneSourceClock := by
  rw [three_pass_slope_exact, bootstrapSteps_eq]; rfl

theorem bs32_standalone_slope3_below_yukon :
    0 < bs32StandaloneSlope3K ∧ bs32StandaloneSlope3K < BlockVsTxSixPassTargetCert.yukonCeiling := by decide

theorem bs32_standalone_slope3_one_tick_tight :
    ¬ bs32StandaloneSlope3K ≤ bs32StandaloneSlope3K - 1 := by decide

theorem bs32_standalone_slope3_saturated_one_tick_tight :
    ¬ bootstrapSteps + bs32_standalone_slope3_postSteps ≤ bs32StandaloneSlope3K - 1 := by
  rw [← bs32_standalone_slope3_decomposition]; exact bs32_standalone_slope3_one_tick_tight

theorem bs32_standalone_slope3_target_bound (sourceTicks targetPost : Nat)
    (hsource : sourceTicks ≤ bs32StandaloneSourceClock)
    (hexpand : targetPost ≤ 3 * sourceTicks) :
    bootstrapSteps + targetPost ≤ bs32StandaloneSlope3K := by
  rw [bs32_standalone_slope3_decomposition]
  exact Nat.add_le_add_left (le_trans hexpand (Nat.mul_le_mul_left 3 hsource)) _

theorem bs32_standalone_slope3_score_representable (minutes : Nat) :
    yukonScore bs32StandaloneSlope3K minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := bs32_standalone_slope3_below_yukon.2
  unfold BlockVsTxSixPassTargetCert.yukonCeiling at h
  omega

/-- Conditional on compilation and uniform target non-timeout. -/
theorem bs32_standalone_slope3_finite_certificate
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
        bs32StandaloneSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK bs32StandaloneSlope3K) (.finite bs32StandaloneSlope3K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (bs32_standalone_slope3_postSteps) hlab compiled depthBound
    (by simpa only [← bs32_standalone_slope3_decomposition] using not_timeOut)
  simpa only [← bs32_standalone_slope3_decomposition] using cert


def bs32TotalSlope3K : Nat := 23_132 + 3 * bs32TotalSourceClock
def bs32_total_slope3_postSteps : Nat := 3 * bs32TotalSourceClock

theorem bs32_total_slope3_exact : bs32TotalSlope3K = 387_840_417_875 := by decide

theorem bs32_total_slope3_decomposition :
    bs32TotalSlope3K = bootstrapSteps + bs32_total_slope3_postSteps := by
  rw [bootstrapSteps_eq]; rfl

theorem bs32_total_slope3_slope_formula :
    bs32TotalSlope3K = bootstrapSteps + threePassSlope * bs32TotalSourceClock := by
  rw [three_pass_slope_exact, bootstrapSteps_eq]; rfl

theorem bs32_total_slope3_below_yukon :
    0 < bs32TotalSlope3K ∧ bs32TotalSlope3K < BlockVsTxSixPassTargetCert.yukonCeiling := by decide

theorem bs32_total_slope3_one_tick_tight :
    ¬ bs32TotalSlope3K ≤ bs32TotalSlope3K - 1 := by decide

theorem bs32_total_slope3_saturated_one_tick_tight :
    ¬ bootstrapSteps + bs32_total_slope3_postSteps ≤ bs32TotalSlope3K - 1 := by
  rw [← bs32_total_slope3_decomposition]; exact bs32_total_slope3_one_tick_tight

theorem bs32_total_slope3_target_bound (sourceTicks targetPost : Nat)
    (hsource : sourceTicks ≤ bs32TotalSourceClock)
    (hexpand : targetPost ≤ 3 * sourceTicks) :
    bootstrapSteps + targetPost ≤ bs32TotalSlope3K := by
  rw [bs32_total_slope3_decomposition]
  exact Nat.add_le_add_left (le_trans hexpand (Nat.mul_le_mul_left 3 hsource)) _

theorem bs32_total_slope3_score_representable (minutes : Nat) :
    yukonScore bs32TotalSlope3K minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := bs32_total_slope3_below_yukon.2
  unfold BlockVsTxSixPassTargetCert.yukonCeiling at h
  omega

/-- Conditional on compilation and uniform target non-timeout. -/
theorem bs32_total_slope3_finite_certificate
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
        bs32TotalSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK bs32TotalSlope3K) (.finite bs32TotalSlope3K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (bs32_total_slope3_postSteps) hlab compiled depthBound
    (by simpa only [← bs32_total_slope3_decomposition] using not_timeOut)
  simpa only [← bs32_total_slope3_decomposition] using cert


def bs32StandaloneSlope6K : Nat := 23_132 + 6 * bs32StandaloneSourceClock
def bs32_standalone_slope6_postSteps : Nat := 6 * bs32StandaloneSourceClock

theorem bs32_standalone_slope6_exact : bs32StandaloneSlope6K = 593_385_979_964 := by decide

theorem bs32_standalone_slope6_decomposition :
    bs32StandaloneSlope6K = bootstrapSteps + bs32_standalone_slope6_postSteps := by
  rw [bootstrapSteps_eq]; rfl

theorem bs32_standalone_slope6_slope_formula :
    bs32StandaloneSlope6K = bootstrapSteps + sixPassSlope * bs32StandaloneSourceClock := by
  rw [six_pass_slope_exact, bootstrapSteps_eq]; rfl

theorem bs32_standalone_slope6_below_yukon :
    0 < bs32StandaloneSlope6K ∧ bs32StandaloneSlope6K < BlockVsTxSixPassTargetCert.yukonCeiling := by decide

theorem bs32_standalone_slope6_one_tick_tight :
    ¬ bs32StandaloneSlope6K ≤ bs32StandaloneSlope6K - 1 := by decide

theorem bs32_standalone_slope6_saturated_one_tick_tight :
    ¬ bootstrapSteps + bs32_standalone_slope6_postSteps ≤ bs32StandaloneSlope6K - 1 := by
  rw [← bs32_standalone_slope6_decomposition]; exact bs32_standalone_slope6_one_tick_tight

theorem bs32_standalone_slope6_target_bound (sourceTicks targetPost : Nat)
    (hsource : sourceTicks ≤ bs32StandaloneSourceClock)
    (hexpand : targetPost ≤ 6 * sourceTicks) :
    bootstrapSteps + targetPost ≤ bs32StandaloneSlope6K := by
  rw [bs32_standalone_slope6_decomposition]
  exact Nat.add_le_add_left (le_trans hexpand (Nat.mul_le_mul_left 6 hsource)) _

theorem bs32_standalone_slope6_score_representable (minutes : Nat) :
    yukonScore bs32StandaloneSlope6K minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := bs32_standalone_slope6_below_yukon.2
  unfold BlockVsTxSixPassTargetCert.yukonCeiling at h
  omega

/-- Conditional on compilation and uniform target non-timeout. -/
theorem bs32_standalone_slope6_finite_certificate
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
        bs32StandaloneSlope6K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK bs32StandaloneSlope6K) (.finite bs32StandaloneSlope6K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (bs32_standalone_slope6_postSteps) hlab compiled depthBound
    (by simpa only [← bs32_standalone_slope6_decomposition] using not_timeOut)
  simpa only [← bs32_standalone_slope6_decomposition] using cert


def bs32TotalSlope6K : Nat := 23_132 + 6 * bs32TotalSourceClock
def bs32_total_slope6_postSteps : Nat := 6 * bs32TotalSourceClock

theorem bs32_total_slope6_exact : bs32TotalSlope6K = 775_680_812_618 := by decide

theorem bs32_total_slope6_decomposition :
    bs32TotalSlope6K = bootstrapSteps + bs32_total_slope6_postSteps := by
  rw [bootstrapSteps_eq]; rfl

theorem bs32_total_slope6_slope_formula :
    bs32TotalSlope6K = bootstrapSteps + sixPassSlope * bs32TotalSourceClock := by
  rw [six_pass_slope_exact, bootstrapSteps_eq]; rfl

theorem bs32_total_slope6_below_yukon :
    0 < bs32TotalSlope6K ∧ bs32TotalSlope6K < BlockVsTxSixPassTargetCert.yukonCeiling := by decide

theorem bs32_total_slope6_one_tick_tight :
    ¬ bs32TotalSlope6K ≤ bs32TotalSlope6K - 1 := by decide

theorem bs32_total_slope6_saturated_one_tick_tight :
    ¬ bootstrapSteps + bs32_total_slope6_postSteps ≤ bs32TotalSlope6K - 1 := by
  rw [← bs32_total_slope6_decomposition]; exact bs32_total_slope6_one_tick_tight

theorem bs32_total_slope6_target_bound (sourceTicks targetPost : Nat)
    (hsource : sourceTicks ≤ bs32TotalSourceClock)
    (hexpand : targetPost ≤ 6 * sourceTicks) :
    bootstrapSteps + targetPost ≤ bs32TotalSlope6K := by
  rw [bs32_total_slope6_decomposition]
  exact Nat.add_le_add_left (le_trans hexpand (Nat.mul_le_mul_left 6 hsource)) _

theorem bs32_total_slope6_score_representable (minutes : Nat) :
    yukonScore bs32TotalSlope6K minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := bs32_total_slope6_below_yukon.2
  unfold BlockVsTxSixPassTargetCert.yukonCeiling at h
  omega

/-- Conditional on compilation and uniform target non-timeout. -/
theorem bs32_total_slope6_finite_certificate
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
        bs32TotalSlope6K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK bs32TotalSlope6K) (.finite bs32TotalSlope6K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (bs32_total_slope6_postSteps) hlab compiled depthBound
    (by simpa only [← bs32_total_slope6_decomposition] using not_timeOut)
  simpa only [← bs32_total_slope6_decomposition] using cert


#print axioms three_pass_slope_exact
#print axioms six_pass_slope_exact
#print axioms bs32_max_probe_exact
#print axioms bs32_probe_bound
#print axioms bs32_probe_attained
#print axioms bs32_probe_one_tick_tight
#print axioms bs32_total_source_exact
#print axioms bs32_standalone_source_exact
#print axioms bs32_total_decomposition
#print axioms bs32_standalone_decomposition
#print axioms block_read_component
#print axioms linear_component
#print axioms bs32_standalone_source_bound
#print axioms bs32_total_source_bound
#print axioms bs32_standalone_slope3_exact
#print axioms bs32_standalone_slope3_decomposition
#print axioms bs32_standalone_slope3_slope_formula
#print axioms bs32_standalone_slope3_below_yukon
#print axioms bs32_standalone_slope3_one_tick_tight
#print axioms bs32_standalone_slope3_saturated_one_tick_tight
#print axioms bs32_standalone_slope3_target_bound
#print axioms bs32_standalone_slope3_score_representable
#print axioms bs32_standalone_slope3_finite_certificate
#print axioms bs32_total_slope3_exact
#print axioms bs32_total_slope3_decomposition
#print axioms bs32_total_slope3_slope_formula
#print axioms bs32_total_slope3_below_yukon
#print axioms bs32_total_slope3_one_tick_tight
#print axioms bs32_total_slope3_saturated_one_tick_tight
#print axioms bs32_total_slope3_target_bound
#print axioms bs32_total_slope3_score_representable
#print axioms bs32_total_slope3_finite_certificate
#print axioms bs32_standalone_slope6_exact
#print axioms bs32_standalone_slope6_decomposition
#print axioms bs32_standalone_slope6_slope_formula
#print axioms bs32_standalone_slope6_below_yukon
#print axioms bs32_standalone_slope6_one_tick_tight
#print axioms bs32_standalone_slope6_saturated_one_tick_tight
#print axioms bs32_standalone_slope6_target_bound
#print axioms bs32_standalone_slope6_score_representable
#print axioms bs32_standalone_slope6_finite_certificate
#print axioms bs32_total_slope6_exact
#print axioms bs32_total_slope6_decomposition
#print axioms bs32_total_slope6_slope_formula
#print axioms bs32_total_slope6_below_yukon
#print axioms bs32_total_slope6_one_tick_tight
#print axioms bs32_total_slope6_saturated_one_tick_tight
#print axioms bs32_total_slope6_target_bound
#print axioms bs32_total_slope6_score_representable
#print axioms bs32_total_slope6_finite_certificate

end InitECandidate.Solver.Bs32DominanceSixPassTargetCert
