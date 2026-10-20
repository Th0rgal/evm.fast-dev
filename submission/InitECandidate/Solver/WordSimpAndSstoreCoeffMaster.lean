import InitECandidate.Solver.WordSimpPreservesNoStoreConsts
import InitECandidate.Solver.GuestSstoreWarmCoeffAudit
import InitECandidate.Solver.SsaCseAndBs32BridgeMaster

set_option autoImplicit false
set_option maxRecDepth 200000

/-! Syntactic NoSt preservation supplies zero store-constant allowance, hence the
unit stack-removal offset. Arithmetic envelopes remain conditional source models;
target certificates require compilation and uniform non-timeout evidence. -/
namespace InitECandidate.Solver.WordSimpAndSstoreCoeffMaster
open InitE Flapjack
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver
open SelfContainedBoundedCertificate WordPassesPreserveNoStoreConsts
open _root_.InitECandidate.Solver.GuestCoupledTxBlockStorageBound (kPanCoupled)
open _root_.InitECandidate.Solver.Bs32EnvelopeTwelveCandidateBridge (yukonCeiling)

noncomputable def simpChain {w : Nat} [NeZero w] (ctx : Spt Nat)
    (q : HolLoopProg w) (l : Nat × Nat) (c : AsmConfigExact w)
    (temp argc : Nat) (b : Bool) :=
  SsaCseAndBs32BridgeMaster.sourceChain c temp argc b
    (WordSimp.compileExp (LoopToWord.compHOL ctx q l).1)

section Chain
variable {w : Nat} [NeZero w] (ctx : Spt Nat) (q : HolLoopProg w)
    (l : Nat × Nat) (c : AsmConfigExact w) (temp argc : Nat) (b : Bool)

theorem simp_chain_non_vacuous_and_tight :
    NoSt (simpChain ctx q l c temp argc b) = true :=
  WordSimpPreservesNoStoreConsts.t_loopToWord_simp_chain ctx q l c temp argc b

theorem boolean_allowance_non_vacuous_and_tight :
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance (simpChain ctx q l c temp argc b) = 0 :=
  WordSimpPreservesNoStoreConsts.allowance_zero_through_simp ctx q l c temp argc b

theorem recursive_allowance_non_vacuous_and_tight :
    StackRemoveStoreConstsZeroBridge.storeConstsAllowance (simpChain ctx q l c temp argc b) = 0 :=
  WordToWordTailNoStoreConstsBridge.noSt_allowance_zero _
    (simp_chain_non_vacuous_and_tight ctx q l c temp argc b)

theorem remove_must_terminate_non_vacuous_and_tight :
    NoSt (WordRemove.removeMustTerminate (simpChain ctx q l c temp argc b)) = true :=
  t_removeMustTerminate _ (simp_chain_non_vacuous_and_tight ctx q l c temp argc b)

theorem stack_clock_non_vacuous_and_tight (k_sn : Nat) :
    SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance k_sn
      (simpChain ctx q l c temp argc b) = k_sn + 1 := by
  unfold SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance
  rw [recursive_allowance_non_vacuous_and_tight ctx q l c temp argc b, Nat.add_zero]

theorem slope_bridge_non_vacuous_and_tight (k_sn : Nat) :
    SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance k_sn
      (simpChain ctx q l c temp argc b) = k_sn + 1 ∧
    SelfContainedQuadraticEnvelopeCert.C_sr_probe = 1 ∧
    SelfContainedSixPassMaster.sixPassSlope SelfContainedQuadraticEnvelopeCert.C_sr_probe 3 = 3 ∧
    SelfContainedSixPassMaster.sixPassSlope SelfContainedQuadraticEnvelopeCert.C_sr_probe 6 = 6 :=
  ⟨stack_clock_non_vacuous_and_tight ctx q l c temp argc b k_sn, rfl, rfl, rfl⟩
end Chain

def coupledSlope3K : Nat := 23132 + 3 * kPanCoupled
def coupledSlope6K : Nat := 23132 + 6 * kPanCoupled

theorem coeffs_non_vacuous_and_tight :
    GuestSstoreWarmCoeffAudit.cnt .localStor (GuestSstoreWarmCoeffAudit.sstoreWarm true) *
      GuestSloadExactProbeTicks.pFind = 10 ∧
    GuestSstoreWarmCoeffAudit.cnt .blockStor (GuestSstoreWarmCoeffAudit.sstoreWarm true) *
      GuestSloadExactProbeTicks.pFind = 2 := GuestSstoreWarmCoeffAudit.coeffs_certified

theorem shortcircuit_non_vacuous_and_tight :
    GuestSstoreWarmCoeffAudit.cnt .blockStor (GuestSstoreWarmCoeffAudit.getStorage true) = 0 ∧
    GuestSstoreWarmCoeffAudit.cnt .blockStor (GuestSstoreWarmCoeffAudit.getStorage false) = 1 :=
  GuestSstoreWarmCoeffAudit.getStorage_shortcircuit

theorem multi_addr_non_vacuous_and_tight (xs : List (Nat × Nat)) :
    (xs.map (fun p => p.1 * p.2)).sum ≤ (xs.map Prod.fst).sum * (xs.map Prod.snd).sum :=
  GuestSstoreWarmCoeffAudit.multi_addr xs

theorem multi_addr_saturation_non_vacuous_and_tight (d w : Nat) :
    ([(d,w)].map (fun p => p.1 * p.2)).sum =
      ([(d,w)].map Prod.fst).sum * ([(d,w)].map Prod.snd).sum :=
  GuestSstoreWarmCoeffAudit.multi_addr_tight d w

theorem coupled_values_non_vacuous_and_tight :
    kPanCoupled = 130854230896 ∧ coupledSlope3K = 392562715820 ∧
    coupledSlope6K = 785125408508 := by decide

theorem target_budget_non_vacuous_and_tight :
    coupledSlope6K = 785125408508 ∧ coupledSlope6K < yukonCeiling :=
  GuestSstoreWarmCoeffAudit.target_budget

theorem margins_non_vacuous_and_tight :
    yukonCeiling - coupledSlope3K = 508157209654 ∧
    yukonCeiling - coupledSlope6K = 115594516966 :=
  ⟨by decide, GuestSstoreWarmCoeffAudit.target_margin⟩

theorem coupled_ceiling_non_vacuous_and_tight :
    0 < coupledSlope3K ∧ coupledSlope3K < coupledSlope6K ∧
    coupledSlope6K < yukonCeiling := by decide

theorem saturated_non_vacuous_and_tight :
    ¬ 23132 + 3 * kPanCoupled ≤ coupledSlope3K - 1 ∧
    ¬ 23132 + 6 * kPanCoupled ≤ coupledSlope6K - 1 := by decide

theorem source_to_target_non_vacuous_and_tight (ticks post : Nat)
    (h : ticks ≤ kPanCoupled) (he : post ≤ 6 * ticks) :
    bootstrapSteps + post ≤ coupledSlope6K := by
  rw [bootstrapSteps_eq]
  exact Nat.add_le_add_left (le_trans he (Nat.mul_le_mul_left 6 h)) _

def masterBudgets : List Nat :=
  [1212035192, 2038701869, 11029669988, 11029683788, 19392692330,
   22059330644, 22059344444, 32791963724, 87829684748, 121459456007,
   122620608536, 214346021162, 242918888882, coupledSlope3K, 428692019192,
   459244490549, 485837754632, 500060306876, 593385979964, 610978715738,
   610978730738, 677645382458, 677645397458, 775680812618, coupledSlope6K,
   857384015252, 857679003380]

theorem full_order_non_vacuous_and_tight :
    (masterBudgets ++ [yukonCeiling]).Pairwise (· < ·) := by decide

theorem master_count_non_vacuous_and_tight : masterBudgets.length = 27 := by decide

theorem previous_portfolio_non_vacuous_and_tight :
    ∀ k ∈ SsaCseAndBs32BridgeMaster.masterBudgets, k ∈ masterBudgets := by decide

theorem coupled_members_non_vacuous_and_tight :
    coupledSlope3K ∈ masterBudgets ∧ coupledSlope6K ∈ masterBudgets := by decide

theorem master_certificate_lift_non_vacuous_and_tight (k : Nat)
    (hk : k ∈ masterBudgets)
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  apply UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight 1212035192 k _ hc
  simp only [masterBudgets, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem three_conditional_certificate_non_vacuous_and_tight
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
        coupledSlope3K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK coupledSlope3K) (.finite coupledSlope3K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (3 * kPanCoupled) hlab compiled depthBound
    (by simpa only [bootstrapSteps_eq, coupledSlope3K] using not_timeOut)
  simpa only [bootstrapSteps_eq, coupledSlope3K] using cert

theorem six_conditional_certificate_non_vacuous_and_tight
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
        coupledSlope6K (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK coupledSlope6K) (.finite coupledSlope6K) := by
  have cert := finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (6 * kPanCoupled) hlab compiled depthBound
    (by simpa only [bootstrapSteps_eq, coupledSlope6K] using not_timeOut)
  simpa only [bootstrapSteps_eq, coupledSlope6K] using cert

#print axioms simp_chain_non_vacuous_and_tight
#print axioms boolean_allowance_non_vacuous_and_tight
#print axioms recursive_allowance_non_vacuous_and_tight
#print axioms remove_must_terminate_non_vacuous_and_tight
#print axioms stack_clock_non_vacuous_and_tight
#print axioms slope_bridge_non_vacuous_and_tight
#print axioms coeffs_non_vacuous_and_tight
#print axioms shortcircuit_non_vacuous_and_tight
#print axioms multi_addr_non_vacuous_and_tight
#print axioms multi_addr_saturation_non_vacuous_and_tight
#print axioms coupled_values_non_vacuous_and_tight
#print axioms target_budget_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms coupled_ceiling_non_vacuous_and_tight
#print axioms saturated_non_vacuous_and_tight
#print axioms source_to_target_non_vacuous_and_tight
#print axioms full_order_non_vacuous_and_tight
#print axioms master_count_non_vacuous_and_tight
#print axioms previous_portfolio_non_vacuous_and_tight
#print axioms coupled_members_non_vacuous_and_tight
#print axioms master_certificate_lift_non_vacuous_and_tight
#print axioms three_conditional_certificate_non_vacuous_and_tight
#print axioms six_conditional_certificate_non_vacuous_and_tight

end InitECandidate.Solver.WordSimpAndSstoreCoeffMaster
