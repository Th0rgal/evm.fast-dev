import InitECandidate.Solver.GuestBs32BlockStorageEnvelope
import InitECandidate.Solver.Bs32DominanceSixPassTargetCert
import InitECandidate.Solver.UnrolledTwelveCandidatePortfolio

set_option autoImplicit false

/-! Arithmetic envelopes are conditional source models, not Guest execution bounds.
Target certificates retain compilation and uniform non-timeout hypotheses.
Tightness refers to the saturated arithmetic envelope. -/
namespace InitECandidate.Solver.Bs32EnvelopeTwelveCandidateBridge
open InitE Flapjack
open InitECandidate.Solver
open SelfContainedBoundedCertificate
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

abbrev threePassSlope : Nat := Bs32DominanceSixPassTargetCert.threePassSlope
abbrev yukonCeiling : Nat := BlockVsTxSixPassTargetCert.yukonCeiling

theorem slope_non_vacuous_and_tight : threePassSlope = 3 :=
  Bs32DominanceSixPassTargetCert.three_pass_slope_exact

theorem source_values_non_vacuous_and_tight :
    GuestBs32BlockStorageEnvelope.kPanBs32Joint = 153_081_489_139 ∧
    GuestBs32BlockStorageEnvelope.kPanBs32Sum = 166_686_761_248 :=
  GuestBs32BlockStorageEnvelope.kPan_values

theorem slope_threshold_non_vacuous_and_tight (k : Nat) :
    k * GuestBs32BlockStorageEnvelope.kPanBs32Joint < yukonCeiling ↔ k ≤ 5 :=
  GuestBs32BlockStorageEnvelope.slope_threshold k

def bs32JointPostSteps : Nat := 3 * GuestBs32BlockStorageEnvelope.kPanBs32Joint
def bs32JointSlope3K : Nat := 23_132 + bs32JointPostSteps

theorem joint_exact_non_vacuous_and_tight : bs32JointSlope3K = 459_244_490_549 := by decide

theorem joint_decomposition_non_vacuous_and_tight :
    bs32JointSlope3K = bootstrapSteps + bs32JointPostSteps := by
  rw [bootstrapSteps_eq]; rfl

theorem joint_slope_formula_non_vacuous_and_tight :
    bs32JointSlope3K = bootstrapSteps + threePassSlope * GuestBs32BlockStorageEnvelope.kPanBs32Joint := by
  rw [slope_non_vacuous_and_tight, bootstrapSteps_eq]; rfl

theorem joint_ceiling_non_vacuous_and_tight :
    0 < bs32JointSlope3K ∧ bs32JointSlope3K < yukonCeiling := by decide

theorem joint_saturated_non_vacuous_and_tight :
    ¬ bootstrapSteps + bs32JointPostSteps ≤ bs32JointSlope3K - 1 := by
  rw [← joint_decomposition_non_vacuous_and_tight]; decide

theorem joint_target_bound_non_vacuous_and_tight (sourceTicks targetPost : Nat)
    (hsource : sourceTicks ≤ GuestBs32BlockStorageEnvelope.kPanBs32Joint) (hexpand : targetPost ≤ 3 * sourceTicks) :
    bootstrapSteps + targetPost ≤ bs32JointSlope3K := by
  rw [joint_decomposition_non_vacuous_and_tight]
  exact Nat.add_le_add_left (le_trans hexpand (Nat.mul_le_mul_left 3 hsource)) _

theorem joint_score_non_vacuous_and_tight (minutes : Nat) :
    yukonScore bs32JointSlope3K minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := joint_ceiling_non_vacuous_and_tight.2
  unfold yukonCeiling BlockVsTxSixPassTargetCert.yukonCeiling at h
  omega

theorem joint_certificate_non_vacuous_and_tight
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
        bs32JointSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth bs32JointPostSteps hlab compiled depthBound
    (by simpa only [← joint_decomposition_non_vacuous_and_tight] using not_timeOut)
  simpa only [← joint_decomposition_non_vacuous_and_tight] using cert

def bs32SumPostSteps : Nat := 3 * GuestBs32BlockStorageEnvelope.kPanBs32Sum
def bs32SumSlope3K : Nat := 23_132 + bs32SumPostSteps

theorem sum_exact_non_vacuous_and_tight : bs32SumSlope3K = 500_060_306_876 := by decide

theorem sum_decomposition_non_vacuous_and_tight :
    bs32SumSlope3K = bootstrapSteps + bs32SumPostSteps := by
  rw [bootstrapSteps_eq]; rfl

theorem sum_slope_formula_non_vacuous_and_tight :
    bs32SumSlope3K = bootstrapSteps + threePassSlope * GuestBs32BlockStorageEnvelope.kPanBs32Sum := by
  rw [slope_non_vacuous_and_tight, bootstrapSteps_eq]; rfl

theorem sum_ceiling_non_vacuous_and_tight :
    0 < bs32SumSlope3K ∧ bs32SumSlope3K < yukonCeiling := by decide

theorem sum_saturated_non_vacuous_and_tight :
    ¬ bootstrapSteps + bs32SumPostSteps ≤ bs32SumSlope3K - 1 := by
  rw [← sum_decomposition_non_vacuous_and_tight]; decide

theorem sum_target_bound_non_vacuous_and_tight (sourceTicks targetPost : Nat)
    (hsource : sourceTicks ≤ GuestBs32BlockStorageEnvelope.kPanBs32Sum) (hexpand : targetPost ≤ 3 * sourceTicks) :
    bootstrapSteps + targetPost ≤ bs32SumSlope3K := by
  rw [sum_decomposition_non_vacuous_and_tight]
  exact Nat.add_le_add_left (le_trans hexpand (Nat.mul_le_mul_left 3 hsource)) _

theorem sum_score_non_vacuous_and_tight (minutes : Nat) :
    yukonScore bs32SumSlope3K minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := sum_ceiling_non_vacuous_and_tight.2
  unfold yukonCeiling BlockVsTxSixPassTargetCert.yukonCeiling at h
  omega

theorem sum_certificate_non_vacuous_and_tight
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
        bs32SumSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK bs32SumSlope3K) (.finite bs32SumSlope3K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth bs32SumPostSteps hlab compiled depthBound
    (by simpa only [← sum_decomposition_non_vacuous_and_tight] using not_timeOut)
  simpa only [← sum_decomposition_non_vacuous_and_tight] using cert

def extendedBudgets : List Nat := UnrolledTwelveCandidatePortfolio.candidates ++
  [bs32JointSlope3K, bs32SumSlope3K,
   Bs32DominanceSixPassTargetCert.bs32StandaloneSlope6K,
   Bs32DominanceSixPassTargetCert.bs32TotalSlope6K,
   UnrolledTwelveCandidatePortfolio.terminalK]

theorem exact_insertion_non_vacuous_and_tight : extendedBudgets =
    UnrolledTwelveCandidatePortfolio.targetBudgets ++
      [459_244_490_549, 500_060_306_876, 593_385_979_964,
       775_680_812_618, 857_384_015_252] := by decide

theorem count_non_vacuous_and_tight : extendedBudgets.length = 17 := by decide

theorem full_ladder_non_vacuous_and_tight : extendedBudgets.Pairwise (· < ·) := by decide

theorem named_insertion_non_vacuous_and_tight :
    1_212_035_192 < BlockVsTxSixPassTargetCert.blockVsTxSlope6K ∧
    BlockVsTxSixPassTargetCert.blockVsTxSlope6K < bs32JointSlope3K ∧
    bs32JointSlope3K < bs32SumSlope3K ∧
    bs32SumSlope3K < Bs32DominanceSixPassTargetCert.bs32StandaloneSlope6K ∧
    Bs32DominanceSixPassTargetCert.bs32StandaloneSlope6K <
      Bs32DominanceSixPassTargetCert.bs32TotalSlope6K ∧
    Bs32DominanceSixPassTargetCert.bs32TotalSlope6K < UnrolledTwelveCandidatePortfolio.terminalK ∧
    UnrolledTwelveCandidatePortfolio.terminalK < yukonCeiling := by decide

theorem all_twelve_below_joint_non_vacuous_and_tight (k : Nat)
    (hk : k ∈ UnrolledTwelveCandidatePortfolio.candidates) : k < bs32JointSlope3K := by
  rw [UnrolledTwelveCandidatePortfolio.candidate_values_non_vacuous_and_tight] at hk
  simp only [UnrolledTwelveCandidatePortfolio.targetBudgets, List.mem_cons,
    List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem margins_non_vacuous_and_tight :
    yukonCeiling - bs32JointSlope3K = 441_475_434_925 ∧
    yukonCeiling - bs32SumSlope3K = 400_659_618_598 ∧
    yukonCeiling < 2 * bs32JointSlope3K := by decide

theorem partition_target_non_vacuous_and_tight (D W C T2 targetPost : Nat)
    (hbudget : 21 * D + W + 21 * C ≤ GuestBs32BlockStorageEnvelope.S)
    (htx : T2 ≤ GuestBs32BlockStorageEnvelope.perTx)
    (hexpand : targetPost ≤ 3 * (GuestBs32BlockStorageEnvelope.linear + T2 +
      (2 * (D * W) + GuestBlockVsTxHtabBounds.blkRead C))) :
    bootstrapSteps + targetPost ≤ bs32JointSlope3K :=
  joint_target_bound_non_vacuous_and_tight _ _
    (GuestBs32BlockStorageEnvelope.kPan_master D W C T2 hbudget htx) hexpand

theorem joint_to_sum_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt bs32JointSlope3K) :
    InitE.Certificate (baselineWithFiniteK bs32SumSlope3K) (.finite bs32SumSlope3K) :=
  UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight _ _ (by decide) hc

#print axioms slope_non_vacuous_and_tight
#print axioms source_values_non_vacuous_and_tight
#print axioms slope_threshold_non_vacuous_and_tight
#print axioms joint_exact_non_vacuous_and_tight
#print axioms joint_decomposition_non_vacuous_and_tight
#print axioms joint_slope_formula_non_vacuous_and_tight
#print axioms joint_ceiling_non_vacuous_and_tight
#print axioms joint_saturated_non_vacuous_and_tight
#print axioms joint_target_bound_non_vacuous_and_tight
#print axioms joint_score_non_vacuous_and_tight
#print axioms joint_certificate_non_vacuous_and_tight
#print axioms sum_exact_non_vacuous_and_tight
#print axioms sum_decomposition_non_vacuous_and_tight
#print axioms sum_slope_formula_non_vacuous_and_tight
#print axioms sum_ceiling_non_vacuous_and_tight
#print axioms sum_saturated_non_vacuous_and_tight
#print axioms sum_target_bound_non_vacuous_and_tight
#print axioms sum_score_non_vacuous_and_tight
#print axioms sum_certificate_non_vacuous_and_tight
#print axioms exact_insertion_non_vacuous_and_tight
#print axioms count_non_vacuous_and_tight
#print axioms full_ladder_non_vacuous_and_tight
#print axioms named_insertion_non_vacuous_and_tight
#print axioms all_twelve_below_joint_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms partition_target_non_vacuous_and_tight
#print axioms joint_to_sum_certificate_non_vacuous_and_tight

end InitECandidate.Solver.Bs32EnvelopeTwelveCandidateBridge
