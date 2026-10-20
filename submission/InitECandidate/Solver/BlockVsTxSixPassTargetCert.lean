import InitECandidate.Solver.GuestBlockVsTxHtabBounds
import InitECandidate.Solver.StackRemoveStoreConstsZeroBridge
import InitECandidate.Solver.PerTxEip7825TargetMasterK

set_option autoImplicit false

/-! Arithmetic certificates for the imported block/transaction model.
The imported gas/probe envelope is a model, not a Guest-wide semantic proof.
Target expansion (including all offsets) and uniform non-timeout remain explicit
obligations; zero structural store-constant allowance alone does not prove them.
No finite certificate is asserted without compiler and target obligations. -/
namespace InitECandidate.Solver.BlockVsTxSixPassTargetCert
open InitE Flapjack
open InitECandidate.Solver
open SelfContainedBoundedCertificate SelfContainedSixPassMaster
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target

def blockVsTxSourceK : Nat := 71_448_666_010
def yukonCeiling : Nat := 900_719_925_474
def blockVsTxSlope3K : Nat := 23_132 + 3 * blockVsTxSourceK
def blockVsTxSlope6K : Nat := 23_132 + 6 * blockVsTxSourceK
def blockVsTxSlope12K : Nat := 23_132 + 12 * blockVsTxSourceK

theorem block_source_bound (c : Nat)
    (h : 2100 * c ≤ GuestEvmStepOpcodeBounds.gasCap) :
    GuestBlockVsTxHtabBounds.kPanBlock c ≤ blockVsTxSourceK :=
  (GuestBlockVsTxHtabBounds.kPanBlock_le_max c h).1

theorem block_source_tight :
    GuestBlockVsTxHtabBounds.kPanBlock GuestBlockVsTxHtabBounds.maxColdPerBlock =
      blockVsTxSourceK := GuestBlockVsTxHtabBounds.kPanBlock_tight.1

theorem sstore_probe_slope : GuestBlockVsTxHtabBounds.pSstore = 14 :=
  GuestBlockVsTxHtabBounds.constants.2.2.1

theorem block_read_exact :
    GuestBlockVsTxHtabBounds.blkRead GuestBlockVsTxHtabBounds.maxColdPerBlock =
      13_605_272_109 :=
  (GuestBlockVsTxHtabBounds.blkRead_le GuestBlockVsTxHtabBounds.maxColdPerBlock (by decide)).2

theorem push31_linear_exact :
    SelfContainedMasterK.prologueTicks + 18 * GuestEvmStepOpcodeBounds.gasCap =
      3_659_564_234 := PerTxEip7825TargetMasterK.per_tx_push31_exact

theorem per_tx_source_strictly_smaller :
    PerTxEip7825TargetMasterK.perTxSourceK < blockVsTxSourceK := by decide

theorem compiled_allowance_zero {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (labels : Nat × Nat) :
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance
      (LoopToWord.compHOL ctx p labels).1 = 0 :=
  StackRemoveStoreConstsZeroBridge.compiled_allowance_zero ctx p labels

theorem allowance_payload_tight {α : Type} (a b c d : Nat) (ws : List (Bool × α)) :
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance
      (.storeConsts a b c d ws) = ws.length :=
  StackRemoveStoreConstsZeroBridge.allowance_storeConsts_tight a b c d ws

theorem slope3_reduction : sixPassSlope 1 3 = 3 :=
  StackRemoveStoreConstsZeroBridge.neutral_six_pass_slope

theorem slope6_reduction : sixPassSlope 1 6 = 6 := by
  rw [six_pass_slope_reduction]

theorem slope12_reduction : sixPassSlope 2 6 = 12 := by
  rw [six_pass_slope_reduction]

theorem slope3_exact : blockVsTxSlope3K = 214346021162 := by decide

theorem slope3_formula :
    blockVsTxSlope3K = bootstrapSteps + 3 * blockVsTxSourceK := by
  rw [bootstrapSteps_eq]; rfl

theorem slope3_below_yukon :
    0 < blockVsTxSlope3K ∧ blockVsTxSlope3K < yukonCeiling := by decide

/-- Expansion must include every additive compiler offset. -/
theorem slope3_target_bound (c sourceTicks targetPost : Nat)
    (hgas : 2100 * c ≤ GuestEvmStepOpcodeBounds.gasCap)
    (hsource : sourceTicks ≤ GuestBlockVsTxHtabBounds.kPanBlock c)
    (hexpand : targetPost ≤ 3 * sourceTicks) :
    bootstrapSteps + targetPost ≤ blockVsTxSlope3K := by
  rw [slope3_formula]
  exact Nat.add_le_add_left
    (le_trans hexpand (Nat.mul_le_mul_left 3 (le_trans hsource (block_source_bound c hgas)))) _

theorem slope3_saturated :
    bootstrapSteps + 3 *
      GuestBlockVsTxHtabBounds.kPanBlock GuestBlockVsTxHtabBounds.maxColdPerBlock =
      blockVsTxSlope3K := by
  rw [block_source_tight, slope3_formula]

theorem slope3_score_representable (minutes : Nat) :
    yukonScore blockVsTxSlope3K minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := slope3_below_yukon.2
  unfold yukonCeiling at h
  omega

theorem slope6_exact : blockVsTxSlope6K = 428692019192 := by decide

theorem slope6_formula :
    blockVsTxSlope6K = bootstrapSteps + 6 * blockVsTxSourceK := by
  rw [bootstrapSteps_eq]; rfl

theorem slope6_below_yukon :
    0 < blockVsTxSlope6K ∧ blockVsTxSlope6K < yukonCeiling := by decide

/-- Expansion must include every additive compiler offset. -/
theorem slope6_target_bound (c sourceTicks targetPost : Nat)
    (hgas : 2100 * c ≤ GuestEvmStepOpcodeBounds.gasCap)
    (hsource : sourceTicks ≤ GuestBlockVsTxHtabBounds.kPanBlock c)
    (hexpand : targetPost ≤ 6 * sourceTicks) :
    bootstrapSteps + targetPost ≤ blockVsTxSlope6K := by
  rw [slope6_formula]
  exact Nat.add_le_add_left
    (le_trans hexpand (Nat.mul_le_mul_left 6 (le_trans hsource (block_source_bound c hgas)))) _

theorem slope6_saturated :
    bootstrapSteps + 6 *
      GuestBlockVsTxHtabBounds.kPanBlock GuestBlockVsTxHtabBounds.maxColdPerBlock =
      blockVsTxSlope6K := by
  rw [block_source_tight, slope6_formula]

theorem slope6_score_representable (minutes : Nat) :
    yukonScore blockVsTxSlope6K minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := slope6_below_yukon.2
  unfold yukonCeiling at h
  omega

theorem slope12_exact : blockVsTxSlope12K = 857384015252 := by decide

theorem slope12_formula :
    blockVsTxSlope12K = bootstrapSteps + 12 * blockVsTxSourceK := by
  rw [bootstrapSteps_eq]; rfl

theorem slope12_below_yukon :
    0 < blockVsTxSlope12K ∧ blockVsTxSlope12K < yukonCeiling := by decide

/-- Expansion must include every additive compiler offset. -/
theorem slope12_target_bound (c sourceTicks targetPost : Nat)
    (hgas : 2100 * c ≤ GuestEvmStepOpcodeBounds.gasCap)
    (hsource : sourceTicks ≤ GuestBlockVsTxHtabBounds.kPanBlock c)
    (hexpand : targetPost ≤ 12 * sourceTicks) :
    bootstrapSteps + targetPost ≤ blockVsTxSlope12K := by
  rw [slope12_formula]
  exact Nat.add_le_add_left
    (le_trans hexpand (Nat.mul_le_mul_left 12 (le_trans hsource (block_source_bound c hgas)))) _

theorem slope12_saturated :
    bootstrapSteps + 12 *
      GuestBlockVsTxHtabBounds.kPanBlock GuestBlockVsTxHtabBounds.maxColdPerBlock =
      blockVsTxSlope12K := by
  rw [block_source_tight, slope12_formula]

theorem slope12_score_representable (minutes : Nat) :
    yukonScore blockVsTxSlope12K minutes < 2 ^ 53 - 1 := by
  apply yukonScore_lt_two_pow_53_sub_one
  have h := slope12_below_yukon.2
  unfold yukonCeiling at h
  omega

/-- Exact rational margins: >4.2 and >2.1 respectively. -/
theorem slope3_margin : 42 * blockVsTxSlope3K < 10 * yukonCeiling := by decide

theorem slope6_margin : 21 * blockVsTxSlope6K < 10 * yukonCeiling := by decide

theorem slope12_headroom : yukonCeiling - blockVsTxSlope12K = 43_335_910_222 := by decide

theorem regimes_ordered :
    blockVsTxSlope3K < blockVsTxSlope6K ∧ blockVsTxSlope6K < blockVsTxSlope12K := by decide

theorem per_tx_target_strictly_smaller :
    PerTxEip7825TargetMasterK.perTxSixPassTargetK < blockVsTxSlope6K := by decide

/-- Conditional finite certificate; compiler correctness and target termination
are obligations, not consequences of the numerical model. -/
theorem slope3_finite_certificate
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
        blockVsTxSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope3K) (.finite blockVsTxSlope3K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (3 * blockVsTxSourceK) hlab compiled depthBound
    (by simpa only [← slope3_formula] using not_timeOut)
  simpa only [← slope3_formula] using cert

/-- Conditional finite certificate; compiler correctness and target termination
are obligations, not consequences of the numerical model. -/
theorem slope6_finite_certificate
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
        blockVsTxSlope6K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope6K) (.finite blockVsTxSlope6K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (6 * blockVsTxSourceK) hlab compiled depthBound
    (by simpa only [← slope6_formula] using not_timeOut)
  simpa only [← slope6_formula] using cert

/-- Conditional finite certificate; compiler correctness and target termination
are obligations, not consequences of the numerical model. -/
theorem slope12_finite_certificate
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
        blockVsTxSlope12K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK blockVsTxSlope12K) (.finite blockVsTxSlope12K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (12 * blockVsTxSourceK) hlab compiled depthBound
    (by simpa only [← slope12_formula] using not_timeOut)
  simpa only [← slope12_formula] using cert

#print axioms block_source_bound
#print axioms block_source_tight
#print axioms sstore_probe_slope
#print axioms block_read_exact
#print axioms push31_linear_exact
#print axioms per_tx_source_strictly_smaller
#print axioms compiled_allowance_zero
#print axioms allowance_payload_tight
#print axioms slope3_reduction
#print axioms slope6_reduction
#print axioms slope12_reduction
#print axioms slope3_exact
#print axioms slope3_formula
#print axioms slope3_below_yukon
#print axioms slope3_target_bound
#print axioms slope3_saturated
#print axioms slope3_score_representable
#print axioms slope6_exact
#print axioms slope6_formula
#print axioms slope6_below_yukon
#print axioms slope6_target_bound
#print axioms slope6_saturated
#print axioms slope6_score_representable
#print axioms slope12_exact
#print axioms slope12_formula
#print axioms slope12_below_yukon
#print axioms slope12_target_bound
#print axioms slope12_saturated
#print axioms slope12_score_representable
#print axioms slope3_margin
#print axioms slope6_margin
#print axioms slope12_headroom
#print axioms regimes_ordered
#print axioms per_tx_target_strictly_smaller
#print axioms slope3_finite_certificate
#print axioms slope6_finite_certificate
#print axioms slope12_finite_certificate

end InitECandidate.Solver.BlockVsTxSixPassTargetCert
