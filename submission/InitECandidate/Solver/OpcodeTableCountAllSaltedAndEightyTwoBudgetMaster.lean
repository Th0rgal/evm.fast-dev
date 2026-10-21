import InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster
import InitECandidate.Solver.StackRemoveNoStoreConstsAndSeventySixBudgetCampaignBridge
import InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact arithmetic synthesis of the imported hand-count model, under the
explicit bounded-probe-run assumption. Salting alone does not guarantee that
assumption. These arithmetic estimates are not semantic runtime certificates;
finite certificates remain conditional on the base semantic certificate.
StackRemove adds zero clock except at most one tick on a final halt. -/
namespace InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev Previous := SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318291, 880629318292]
def EightyTwoShape : Prop :=
  portfolio.length = 82 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 80 = Previous ∧
  portfolio.drop 80 = [880629318291, 880629318292] ∧
  portfolio.getLast? = some 880629318292 ∧ yukon = 900719925474

theorem finds_max_and_unit_val_non_vacuous_and_tight :
    (1 + 2 + 2 + 2 = 7 ∧ 1 ≤ 7 ∧ 3 ≤ 7 ∧ 1 + 5 ≤ 7) ∧
    (opTicks 8 = 28 ∧ unitTicks = 336) :=
  ⟨GuestOpcodeTableCountAndAllTablesSaltedMaster.finds_max, GuestOpcodeTableCountAndAllTablesSaltedMaster.unit_val⟩

theorem env_split_and_vals_non_vacuous_and_tight :
    (3659564234 + 500000000 + 151929428571 = 156088992805 ∧
    151929428571 = 100000000000 + 51929428571) ∧
    (env200 = 4831564234 ∧ env380 = 9126364234) :=
  ⟨GuestOpcodeTableCountAndAllTablesSaltedMaster.env_split, GuestOpcodeTableCountAndAllTablesSaltedMaster.env_vals⟩

theorem main200_slope_non_vacuous_and_tight :
    (main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
    yukon < 19 * main200AllSalted) :=
  GuestOpcodeTableCountAndAllTablesSaltedMaster.main200_slope

theorem main380_slope_non_vacuous_and_tight :
    (main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
    yukon < 17 * main380AllSalted) :=
  GuestOpcodeTableCountAndAllTablesSaltedMaster.main380_slope

theorem unit_slack_non_vacuous_and_tight :
    (18 * (3659564234 + 500000000 + 741 * 2000000 + restMain) < yukon ∧
      yukon ≤ 18 * (3659564234 + 500000000 + 742 * 2000000 + restMain) ∧
    16 * (59564234 + 18 * 380000000 + 950000000 + 1065 * 3800000 + restMain) < yukon ∧
      yukon ≤ 16 * (59564234 + 18 * 380000000 + 950000000 + 1066 * 3800000 + restMain)) :=
  GuestOpcodeTableCountAndAllTablesSaltedMaster.unit_slack

theorem run_slack_non_vacuous_and_tight :
    (12 * opTicks 24 ≤ 741 ∧ 741 < 12 * opTicks 25) :=
  GuestOpcodeTableCountAndAllTablesSaltedMaster.run_slack

theorem gain_non_vacuous_and_tight :
    (102485906743 - 49228478172 = 53257428571 ∧
    154766000267 - 53523278172 = 101242722095) :=
  GuestOpcodeTableCountAndAllTablesSaltedMaster.gain

theorem rest_dominates_non_vacuous_and_tight :
    (restMain = 44396913938) ∧
    (10 * restMain > 9 * main200AllSalted) :=
  ⟨GuestOpcodeTableCountAndAllTablesSaltedMaster.rest_val, GuestOpcodeTableCountAndAllTablesSaltedMaster.rest_dominates⟩

theorem panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 = true :=
  SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight arch prog wc ac perf info

theorem panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
        CodeNoSt source →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 pointer →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp jump bounds pointer
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget) :=
  SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight arch prog wc ac perf info

theorem eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    EightyTwoShape := by
  unfold EightyTwoShape
  decide

theorem eighty_two_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyTwoShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms finds_max_and_unit_val_non_vacuous_and_tight
#print axioms env_split_and_vals_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_non_vacuous_and_tight
#print axioms unit_slack_non_vacuous_and_tight
#print axioms run_slack_non_vacuous_and_tight
#print axioms gain_non_vacuous_and_tight
#print axioms rest_dominates_non_vacuous_and_tight
#print axioms panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight
#print axioms panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight
#print axioms eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms eighty_two_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster
