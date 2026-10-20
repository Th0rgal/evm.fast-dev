import InitECandidate.Solver.GuestCoupledTxBlockStorageBound
import InitECandidate.Solver.MidPassesTwelveCandidateMaster
import InitECandidate.Solver.Bs32EnvelopeTwelveCandidateBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-! Conditional arithmetic source envelopes and target certificates. Expansion
includes all compiler offsets; no Guest execution bound follows from syntax.
One-tick tightness concerns the saturated arithmetic envelope only. -/
namespace InitECandidate.Solver.CoupledTxBlockSixPassTargetCert
open InitE Flapjack
open InitECandidate.Solver
open SelfContainedBoundedCertificate
open GuestCoupledTxBlockStorageBound
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

def threePassSlope : Nat := 3
def sixPassSlope : Nat := 6
abbrev yukonCeiling := BlockVsTxSixPassTargetCert.yukonCeiling

theorem slopes_non_vacuous_and_tight : threePassSlope = 3 ∧ sixPassSlope = 6 := by decide

theorem source_non_vacuous_and_tight :
    kPanCoupled = 130854230896 ∧
    kPanCoupled < GuestBs32BlockStorageEnvelope.kPanBs32Joint ∧
    GuestBs32BlockStorageEnvelope.kPanBs32Joint - kPanCoupled = 22227258243 :=
  kPanCoupled_val

def coupledTxBlockSlope3PostSteps : Nat := threePassSlope * kPanCoupled
def coupledTxBlockSlope3K : Nat := 23132 + coupledTxBlockSlope3PostSteps

theorem slope3_exact_non_vacuous_and_tight : coupledTxBlockSlope3K = 392562715820 := by decide

theorem slope3_decomposition_non_vacuous_and_tight :
    coupledTxBlockSlope3K = bootstrapSteps + coupledTxBlockSlope3PostSteps := by
  rw [bootstrapSteps_eq]; rfl

theorem slope3_formula_non_vacuous_and_tight :
    coupledTxBlockSlope3K = bootstrapSteps + threePassSlope * kPanCoupled := by
  rw [bootstrapSteps_eq]; rfl

theorem slope3_ceiling_non_vacuous_and_tight :
    0 < coupledTxBlockSlope3K ∧ coupledTxBlockSlope3K < yukonCeiling := by decide

theorem slope3_one_tick_non_vacuous_and_tight :
    ¬ coupledTxBlockSlope3K ≤ coupledTxBlockSlope3K - 1 := by decide

theorem slope3_saturated_non_vacuous_and_tight :
    ¬ bootstrapSteps + coupledTxBlockSlope3PostSteps ≤ coupledTxBlockSlope3K - 1 := by
  rw [← slope3_decomposition_non_vacuous_and_tight]; decide

theorem slope3_target_bound_non_vacuous_and_tight (sourceTicks targetPost : Nat)
    (hsource : sourceTicks ≤ kPanCoupled) (hexpand : targetPost ≤ threePassSlope * sourceTicks) :
    bootstrapSteps + targetPost ≤ coupledTxBlockSlope3K := by
  rw [slope3_formula_non_vacuous_and_tight]
  exact Nat.add_le_add_left (le_trans hexpand (Nat.mul_le_mul_left _ hsource)) _

theorem slope3_partition_non_vacuous_and_tight (l : List (Nat × Nat)) (C targetPost : Nat)
    (h : ∀ p ∈ l, 21 * p.1 + p.2 ≤ M)
    (hS : sumUnits l + 21 * C ≤ GuestBs32BlockStorageEnvelope.S)
    (hexpand : targetPost ≤ threePassSlope * (GuestBs32BlockStorageEnvelope.linear +
      coupled l 0 + GuestBlockVsTxHtabBounds.blkRead C)) :
    bootstrapSteps + targetPost ≤ coupledTxBlockSlope3K :=
  slope3_target_bound_non_vacuous_and_tight _ _ (kPan_coupled_master l C h hS) hexpand

theorem slope3_certificate_non_vacuous_and_tight
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
        coupledTxBlockSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK coupledTxBlockSlope3K) (.finite coupledTxBlockSlope3K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth coupledTxBlockSlope3PostSteps hlab compiled depthBound
    (by simpa only [← slope3_decomposition_non_vacuous_and_tight] using not_timeOut)
  simpa only [← slope3_decomposition_non_vacuous_and_tight] using cert

def coupledTxBlockSlope6PostSteps : Nat := sixPassSlope * kPanCoupled
def coupledTxBlockSlope6K : Nat := 23132 + coupledTxBlockSlope6PostSteps

theorem slope6_exact_non_vacuous_and_tight : coupledTxBlockSlope6K = 785125408508 := by decide

theorem slope6_decomposition_non_vacuous_and_tight :
    coupledTxBlockSlope6K = bootstrapSteps + coupledTxBlockSlope6PostSteps := by
  rw [bootstrapSteps_eq]; rfl

theorem slope6_formula_non_vacuous_and_tight :
    coupledTxBlockSlope6K = bootstrapSteps + sixPassSlope * kPanCoupled := by
  rw [bootstrapSteps_eq]; rfl

theorem slope6_ceiling_non_vacuous_and_tight :
    0 < coupledTxBlockSlope6K ∧ coupledTxBlockSlope6K < yukonCeiling := by decide

theorem slope6_one_tick_non_vacuous_and_tight :
    ¬ coupledTxBlockSlope6K ≤ coupledTxBlockSlope6K - 1 := by decide

theorem slope6_saturated_non_vacuous_and_tight :
    ¬ bootstrapSteps + coupledTxBlockSlope6PostSteps ≤ coupledTxBlockSlope6K - 1 := by
  rw [← slope6_decomposition_non_vacuous_and_tight]; decide

theorem slope6_target_bound_non_vacuous_and_tight (sourceTicks targetPost : Nat)
    (hsource : sourceTicks ≤ kPanCoupled) (hexpand : targetPost ≤ sixPassSlope * sourceTicks) :
    bootstrapSteps + targetPost ≤ coupledTxBlockSlope6K := by
  rw [slope6_formula_non_vacuous_and_tight]
  exact Nat.add_le_add_left (le_trans hexpand (Nat.mul_le_mul_left _ hsource)) _

theorem slope6_partition_non_vacuous_and_tight (l : List (Nat × Nat)) (C targetPost : Nat)
    (h : ∀ p ∈ l, 21 * p.1 + p.2 ≤ M)
    (hS : sumUnits l + 21 * C ≤ GuestBs32BlockStorageEnvelope.S)
    (hexpand : targetPost ≤ sixPassSlope * (GuestBs32BlockStorageEnvelope.linear +
      coupled l 0 + GuestBlockVsTxHtabBounds.blkRead C)) :
    bootstrapSteps + targetPost ≤ coupledTxBlockSlope6K :=
  slope6_target_bound_non_vacuous_and_tight _ _ (kPan_coupled_master l C h hS) hexpand

theorem slope6_certificate_non_vacuous_and_tight
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
        coupledTxBlockSlope6K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK coupledTxBlockSlope6K) (.finite coupledTxBlockSlope6K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth coupledTxBlockSlope6PostSteps hlab compiled depthBound
    (by simpa only [← slope6_decomposition_non_vacuous_and_tight] using not_timeOut)
  simpa only [← slope6_decomposition_non_vacuous_and_tight] using cert

theorem margins_non_vacuous_and_tight :
    229 * coupledTxBlockSlope3K < 100 * yukonCeiling ∧
    yukonCeiling - coupledTxBlockSlope6K = 115594516966 ∧
    Bs32EnvelopeTwelveCandidateBridge.bs32JointSlope3K - coupledTxBlockSlope3K =
      3 * 22227258243 := by decide

theorem threshold_non_vacuous_and_tight (slope : Nat) :
    bootstrapSteps + slope * kPanCoupled < yukonCeiling ↔ slope ≤ 6 := by
  have hv : kPanCoupled = 130854230896 := kPanCoupled_val.1
  rw [bootstrapSteps_eq, hv]
  change 23132 + slope * 130854230896 < 900719925474 ↔ slope ≤ 6
  omega

def fullCandidates : List Nat :=
  MidPassesTwelveCandidateMaster.unifiedCandidates.take 13 ++
  [coupledTxBlockSlope3K, BlockVsTxSixPassTargetCert.blockVsTxSlope6K,
   Bs32EnvelopeTwelveCandidateBridge.bs32JointSlope3K,
   JointBlockGasSixPassMasterCert.jointBlockGasSlope12K,
   Bs32EnvelopeTwelveCandidateBridge.bs32SumSlope3K,
   Bs32DominanceSixPassTargetCert.bs32StandaloneSlope6K,
   Bs32DominanceSixPassTargetCert.bs32TotalSlope6K, coupledTxBlockSlope6K,
   UnrolledTwelveCandidatePortfolio.terminalK]

def fullBudgets : List Nat :=
  [1212035192,2038701869,11029669988,11029683788,19392692330,
   22059330644,22059344444,32791963724,87829684748,121459456007,
   122620608536,214346021162,242918888882,392562715820,428692019192,
   459244490549,485837754632,500060306876,593385979964,775680812618,
   785125408508,857384015252]

theorem insertion_non_vacuous_and_tight : fullCandidates = fullBudgets := by decide

theorem count_non_vacuous_and_tight : fullCandidates.length = 22 := by decide

theorem ladder_non_vacuous_and_tight : fullCandidates.Pairwise (· < ·) := by decide

theorem named_insertion_non_vacuous_and_tight :
    JointBlockGasSixPassMasterCert.jointBlockGasSlope6K < coupledTxBlockSlope3K ∧
    coupledTxBlockSlope3K < BlockVsTxSixPassTargetCert.blockVsTxSlope6K ∧
    BlockVsTxSixPassTargetCert.blockVsTxSlope6K < Bs32EnvelopeTwelveCandidateBridge.bs32JointSlope3K ∧
    Bs32DominanceSixPassTargetCert.bs32TotalSlope6K < coupledTxBlockSlope6K ∧
    coupledTxBlockSlope6K < UnrolledTwelveCandidatePortfolio.terminalK ∧
    UnrolledTwelveCandidatePortfolio.terminalK < yukonCeiling := by decide

theorem coverage_non_vacuous_and_tight :
    (∀ k ∈ MidPassesTwelveCandidateMaster.unifiedCandidates, k ∈ fullCandidates) ∧
    (∀ k ∈ Bs32EnvelopeTwelveCandidateBridge.extendedBudgets, k ∈ fullCandidates) ∧
    coupledTxBlockSlope3K ∈ fullCandidates ∧ coupledTxBlockSlope6K ∈ fullCandidates := by decide

theorem full_bounds_non_vacuous_and_tight :
    ∀ k ∈ fullCandidates, 1212035192 ≤ k ∧ k < yukonCeiling := by decide

theorem full_one_tick_non_vacuous_and_tight (k : Nat) (hk : k ∈ fullCandidates) :
    ¬ k ≤ k - 1 := by
  have h := (full_bounds_non_vacuous_and_tight k hk).1
  omega

theorem full_certificates_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    ∀ k ∈ fullCandidates, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  intro k hk
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight _ _
    (full_bounds_non_vacuous_and_tight k hk).1 hc

#print axioms slopes_non_vacuous_and_tight
#print axioms source_non_vacuous_and_tight
#print axioms slope3_exact_non_vacuous_and_tight
#print axioms slope3_decomposition_non_vacuous_and_tight
#print axioms slope3_formula_non_vacuous_and_tight
#print axioms slope3_ceiling_non_vacuous_and_tight
#print axioms slope3_one_tick_non_vacuous_and_tight
#print axioms slope3_saturated_non_vacuous_and_tight
#print axioms slope3_target_bound_non_vacuous_and_tight
#print axioms slope3_partition_non_vacuous_and_tight
#print axioms slope3_certificate_non_vacuous_and_tight
#print axioms slope6_exact_non_vacuous_and_tight
#print axioms slope6_decomposition_non_vacuous_and_tight
#print axioms slope6_formula_non_vacuous_and_tight
#print axioms slope6_ceiling_non_vacuous_and_tight
#print axioms slope6_one_tick_non_vacuous_and_tight
#print axioms slope6_saturated_non_vacuous_and_tight
#print axioms slope6_target_bound_non_vacuous_and_tight
#print axioms slope6_partition_non_vacuous_and_tight
#print axioms slope6_certificate_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms threshold_non_vacuous_and_tight
#print axioms insertion_non_vacuous_and_tight
#print axioms count_non_vacuous_and_tight
#print axioms ladder_non_vacuous_and_tight
#print axioms named_insertion_non_vacuous_and_tight
#print axioms coverage_non_vacuous_and_tight
#print axioms full_bounds_non_vacuous_and_tight
#print axioms full_one_tick_non_vacuous_and_tight
#print axioms full_certificates_non_vacuous_and_tight

end InitECandidate.Solver.CoupledTxBlockSixPassTargetCert
