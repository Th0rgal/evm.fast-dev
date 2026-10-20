import InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts
import InitECandidate.Solver.Bs32EnvelopeTwelveCandidateBridge
import InitECandidate.Solver.SelfContainedMidPassesAndSloadSynth

set_option autoImplicit false
set_option maxRecDepth 200000

/-! Arithmetic tightness is saturation of the source envelope. Target certificates
retain compilation and uniform non-timeout premises; NoSt alone is not a target
simulation. The Boolean allowance and recursive payload allowance are related
only on NoSt programs. No bounded-proof imports are used. -/
namespace InitECandidate.Solver.SsaCseAndBs32BridgeMaster
open InitE Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver
open SelfContainedBoundedCertificate WordPassesPreserveNoStoreConsts
open Flapjack.Compiler.Backend.WordAlloc

noncomputable def eightPassChain {w : Nat} [NeZero w] (c : AsmConfigExact w)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec w)) :=
  WordRemove.removeMustTerminate (WordUnreach.removeUnreach
    (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordCse.wordCommonSubexpElim
      (WordAlloc.removeDeadProg (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))

/-- Exact source theorem's additional final dead-code pass, preserved separately. -/
noncomputable def sourceChain {w : Nat} [NeZero w] (c : AsmConfigExact w)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec w)) :=
  WordAlloc.removeDeadProg (WordUnreach.removeUnreach
    (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordCse.wordCommonSubexpElim
      (WordAlloc.removeDeadProg (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))

section Chain
variable {w : Nat} [NeZero w] (c : AsmConfigExact w) (temp argc : Nat)
  (b : Bool) (p : WordLangProgHOL (BitVec w)) (hp : NoSt p = true)
include hp

theorem source_chain_non_vacuous_and_tight :
    NoSt (sourceChain c temp argc b p) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (sourceChain c temp argc b p) = 0 :=
  ⟨WordSsaCsePreserveNoStoreConsts.t_ssa_cse_mid_tail_chain c temp argc b p hp,
   WordSsaCsePreserveNoStoreConsts.storeConstsAllowance_chain_zero c temp argc b p hp⟩

theorem eight_pass_noSt_non_vacuous_and_tight :
    NoSt (eightPassChain c temp argc b p) = true := by
  apply t_removeMustTerminate
  exact t_removeUnreach _ (t_threeToTwo b _ (WordMidPassesPreserveNoStoreConsts.t_copyProp _
    (WordSsaCsePreserveNoStoreConsts.t_wordCommonSubexpElim _
      (WordMidPassesPreserveNoStoreConsts.t_removeDeadProg _
        (WordSsaCsePreserveNoStoreConsts.t_fullSsaCcTrans argc _
          (WordMidPassesPreserveNoStoreConsts.t_instSelect c temp p hp))))))

theorem boolean_allowance_non_vacuous_and_tight :
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (eightPassChain c temp argc b p) = 0 := by
  simp [WordSsaCsePreserveNoStoreConsts.storeConstsAllowance,
    eight_pass_noSt_non_vacuous_and_tight c temp argc b p hp]

theorem recursive_allowance_non_vacuous_and_tight :
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance (eightPassChain c temp argc b p) = 0 :=
  WordToWordTailNoStoreConstsBridge.noSt_allowance_zero _
    (eight_pass_noSt_non_vacuous_and_tight c temp argc b p hp)

theorem stack_remove_clock_non_vacuous_and_tight (k_sn : Nat) :
    SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance k_sn
      (eightPassChain c temp argc b p) = k_sn + 1 := by
  unfold SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance
  rw [recursive_allowance_non_vacuous_and_tight c temp argc b p hp, Nat.add_zero]

theorem slope_bridge_non_vacuous_and_tight (k_sn : Nat) :
    SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance k_sn
      (eightPassChain c temp argc b p) = k_sn + 1 ∧
    SelfContainedQuadraticEnvelopeCert.C_sr_probe = 1 ∧
    Bs32EnvelopeTwelveCandidateBridge.threePassSlope =
      SelfContainedSixPassMaster.sixPassSlope SelfContainedQuadraticEnvelopeCert.C_sr_probe 3 ∧
    Bs32EnvelopeTwelveCandidateBridge.threePassSlope = 3 :=
  ⟨stack_remove_clock_non_vacuous_and_tight c temp argc b p hp k_sn, rfl, rfl,
    Bs32EnvelopeTwelveCandidateBridge.slope_non_vacuous_and_tight⟩

theorem mid_passes_bridge_non_vacuous_and_tight :
    NoSt (eightPassChain c temp argc b p) = true ∧
    NoSt (SelfContainedMidPassesAndSloadSynth.midTailChain c temp b p) = true :=
  ⟨eight_pass_noSt_non_vacuous_and_tight c temp argc b p hp,
    WordMidPassesPreserveNoStoreConsts.t_mid_tail_chain c temp b p hp⟩
end Chain

open Bs32EnvelopeTwelveCandidateBridge

theorem exact_bs32_non_vacuous_and_tight :
    bs32JointSlope3K = 459_244_490_549 ∧ bs32SumSlope3K = 500_060_306_876 :=
  ⟨joint_exact_non_vacuous_and_tight, sum_exact_non_vacuous_and_tight⟩

theorem both_below_ceiling_non_vacuous_and_tight :
    0 < bs32JointSlope3K ∧ bs32JointSlope3K < bs32SumSlope3K ∧
    bs32SumSlope3K < yukonCeiling := by decide

theorem both_saturated_non_vacuous_and_tight :
    ¬ bootstrapSteps + bs32JointPostSteps ≤ bs32JointSlope3K - 1 ∧
    ¬ bootstrapSteps + bs32SumPostSteps ≤ bs32SumSlope3K - 1 :=
  ⟨joint_saturated_non_vacuous_and_tight, sum_saturated_non_vacuous_and_tight⟩

/-- All 17 BS32/portfolio budgets plus the eight additional joint/SLOAD regimes. -/
def masterBudgets : List Nat :=
  [1212035192, 2038701869, 11029669988, 11029683788, 19392692330,
   22059330644, 22059344444, 32791963724, 87829684748,
   JointBlockGasSixPassMasterCert.jointBlockGasSlope3K, 122620608536, 214346021162,
   JointBlockGasSixPassMasterCert.jointBlockGasSlope6K, 428692019192,
   bs32JointSlope3K, JointBlockGasSixPassMasterCert.jointBlockGasSlope12K,
   bs32SumSlope3K, Bs32DominanceSixPassTargetCert.bs32StandaloneSlope6K,
   SelfContainedMidPassesAndSloadSynth.coldSloadProbeZeroOffsetK,
   SelfContainedSloadProbeEnvelope.coldSloadProbeEnvelopeTargetK,
   SelfContainedMidPassesAndSloadSynth.sloadProbeZeroOffsetK,
   SelfContainedSloadProbeEnvelope.sloadProbeEnvelopeTargetK,
   Bs32DominanceSixPassTargetCert.bs32TotalSlope6K,
   UnrolledTwelveCandidatePortfolio.terminalK, SelfContainedQuadraticEnvelopeCert.quadraticCollisionTargetK]

theorem full_order_non_vacuous_and_tight : masterBudgets.Pairwise (· < ·) := by decide

theorem master_count_non_vacuous_and_tight : masterBudgets.length = 25 := by decide

theorem full_ceiling_non_vacuous_and_tight :
    (masterBudgets ++ [yukonCeiling]).Pairwise (· < ·) := by decide

theorem both_scores_non_vacuous_and_tight (minutes : Nat) :
    yukonScore bs32JointSlope3K minutes < 2 ^ 53 - 1 ∧
    yukonScore bs32SumSlope3K minutes < 2 ^ 53 - 1 :=
  ⟨joint_score_non_vacuous_and_tight minutes, sum_score_non_vacuous_and_tight minutes⟩

theorem master_certificate_lift_non_vacuous_and_tight (k : Nat)
    (hk : k ∈ masterBudgets)
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  apply UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight 1212035192 k _ hc
  simp only [masterBudgets, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem joint_conditional_certificate_non_vacuous_and_tight
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
    InitE.Certificate (baselineWithFiniteK bs32JointSlope3K) (.finite bs32JointSlope3K) :=
  joint_certificate_non_vacuous_and_tight oracles c depth hlab compiled depthBound not_timeOut

theorem sum_conditional_certificate_non_vacuous_and_tight
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
    InitE.Certificate (baselineWithFiniteK bs32SumSlope3K) (.finite bs32SumSlope3K) :=
  sum_certificate_non_vacuous_and_tight oracles c depth hlab compiled depthBound not_timeOut

/-- Combined master: the syntactic invariant and arithmetic slope accompany every
conditional certificate in the merged portfolio. The semantic certificate premise
is essential and is not inferred from the syntactic invariant. -/
theorem master_synthesis_non_vacuous_and_tight
    {w : Nat} [NeZero w] (c : AsmConfigExact w) (temp argc : Nat) (b : Bool)
    (p : WordLangProgHOL (BitVec w)) (hp : NoSt p = true) (k_sn : Nat)
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    NoSt (eightPassChain c temp argc b p) = true ∧
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (eightPassChain c temp argc b p) = 0 ∧
    SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance k_sn
      (eightPassChain c temp argc b p) = k_sn + 1 ∧
    SelfContainedQuadraticEnvelopeCert.C_sr_probe = 1 ∧
    threePassSlope = 3 ∧
    bs32JointSlope3K = 459_244_490_549 ∧ bs32SumSlope3K = 500_060_306_876 ∧
    bs32JointSlope3K < bs32SumSlope3K ∧ bs32SumSlope3K < yukonCeiling ∧
    masterBudgets.Pairwise (· < ·) ∧
    (∀ k ∈ masterBudgets, InitE.Certificate (baselineWithFiniteK k) (.finite k)) := by
  exact ⟨eight_pass_noSt_non_vacuous_and_tight c temp argc b p hp,
    boolean_allowance_non_vacuous_and_tight c temp argc b p hp,
    stack_remove_clock_non_vacuous_and_tight c temp argc b p hp k_sn,
    rfl, slope_non_vacuous_and_tight, joint_exact_non_vacuous_and_tight,
    sum_exact_non_vacuous_and_tight, by decide, sum_ceiling_non_vacuous_and_tight.2,
    full_order_non_vacuous_and_tight,
    fun k hk => master_certificate_lift_non_vacuous_and_tight k hk hc⟩

#print axioms source_chain_non_vacuous_and_tight
#print axioms eight_pass_noSt_non_vacuous_and_tight
#print axioms boolean_allowance_non_vacuous_and_tight
#print axioms recursive_allowance_non_vacuous_and_tight
#print axioms stack_remove_clock_non_vacuous_and_tight
#print axioms slope_bridge_non_vacuous_and_tight
#print axioms mid_passes_bridge_non_vacuous_and_tight
#print axioms exact_bs32_non_vacuous_and_tight
#print axioms both_below_ceiling_non_vacuous_and_tight
#print axioms both_saturated_non_vacuous_and_tight
#print axioms full_order_non_vacuous_and_tight
#print axioms master_count_non_vacuous_and_tight
#print axioms full_ceiling_non_vacuous_and_tight
#print axioms both_scores_non_vacuous_and_tight
#print axioms master_certificate_lift_non_vacuous_and_tight
#print axioms joint_conditional_certificate_non_vacuous_and_tight
#print axioms sum_conditional_certificate_non_vacuous_and_tight
#print axioms master_synthesis_non_vacuous_and_tight

end InitECandidate.Solver.SsaCseAndBs32BridgeMaster
