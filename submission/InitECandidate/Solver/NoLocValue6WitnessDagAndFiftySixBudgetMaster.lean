import InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6
import InitECandidate.Solver.SelfContainedWitnessDecodeAndFiftyFourBudgetMaster
import InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_164: section-6 control/address safety, decoded witness bounds, DAG
memoization and the 56-tier Yukon portfolio. Arithmetic uses the imported model
contracts; decoded walks assume at most 64 consumed nibbles. Semantic finite
certificates require the explicit base certificate. -/
namespace InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster

open InitECandidate.Solver
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open StackToLabAndLabToTargetNoLocValue6

abbrev portfolio := WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.portfolio
abbrev fiftySixClaims := WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.fiftySixClaims

def PanTargetSafe : Prop :=
  ∀ {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')),
    ∀ s' ∈ L', PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = true ∨
      ∀ x ∈ s'.lines, JumpOk x = true

def PanUserSafe : Prop :=
  ∀ {width : Nat} [NeZero width] (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (s' : Sec width) (hs : s' ∈ L')
    (hu : PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false),
    ∀ x ∈ s'.lines, JumpOk x = true

variable {width : Nat} [NeZero width]

theorem panToTarget_noStubLoc6_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    ∀ s' ∈ L', PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = true ∨
      ∀ x ∈ s'.lines, JumpOk x = true :=
  panToTarget_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h

theorem panToTarget_user_noStubLoc6_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (s' : Sec width) (hs : s' ∈ L')
    (hu : PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false) :
    ∀ x ∈ s'.lines, JumpOk x = true :=
  panToTarget_user_sections_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu

theorem compact_len_cases_and_compact_zero_iff_non_vacuous_and_tight : SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.CompactContract :=
  SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.compact_len_cases_zero_iff_full_key_non_vacuous_and_tight

theorem ext_zero_rejected_non_vacuous_and_tight : SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.ExtensionContract :=
  SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.ext_zero_child_rejected_and_accepted_advances_non_vacuous_and_tight

theorem walk_bound_decoded_non_vacuous_and_tight : SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.DecodedWalkContract :=
  SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.walk_bound_decoded_non_vacuous_and_tight

theorem expansion_traps_non_vacuous_and_tight : SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.HeapContract :=
  SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.heap_nodes_and_expansion_traps_non_vacuous_and_tight

theorem heap_allocation_non_vacuous_and_tight : WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapAllocationContract :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.heap_allocation_non_vacuous_and_tight

theorem heap_nodes_non_vacuous_and_tight : WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapNodesContract :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.heap_nodes_non_vacuous_and_tight

theorem heap_rates_non_vacuous_and_tight : WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapRateContract :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.heap_rates_non_vacuous_and_tight

theorem memo_non_vacuous_and_tight : WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.MemoContract :=
  WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.memo_non_vacuous_and_tight

theorem fifty_six_portfolio_and_payloads_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.FiftySixShape ∧ WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.ClaimPayloads :=
  ⟨WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.portfolio_non_vacuous_and_tight,
   WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.payloads_non_vacuous_and_tight⟩

/-- All witness and DAG bounds and the increasing portfolio hold unconditionally.
Only the execution certificates below depend on the base certificate. -/
theorem no_loc_value_6_witness_dag_and_fifty_six_budget_master_non_vacuous_and_tight :
    PanTargetSafe ∧ PanUserSafe ∧
    SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.CompactContract ∧
    SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.ExtensionContract ∧
    SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.DecodedWalkContract ∧
    SelfContainedWitnessDecodeAndFiftyFourBudgetMaster.HeapContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapAllocationContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapNodesContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.HeapRateContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.MemoContract ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.FiftySixShape ∧ WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.ClaimPayloads ∧
    (UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192 →
      ∀ K ∈ portfolio,
        InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K) (.finite K)) :=
  ⟨panToTarget_noStubLoc6_non_vacuous_and_tight,
   panToTarget_user_noStubLoc6_non_vacuous_and_tight,
   compact_len_cases_and_compact_zero_iff_non_vacuous_and_tight,
   ext_zero_rejected_non_vacuous_and_tight,
   walk_bound_decoded_non_vacuous_and_tight,
   expansion_traps_non_vacuous_and_tight,
   heap_allocation_non_vacuous_and_tight,
   heap_nodes_non_vacuous_and_tight,
   heap_rates_non_vacuous_and_tight,
   memo_non_vacuous_and_tight,
   fifty_six_portfolio_and_payloads_non_vacuous_and_tight.1,
   fifty_six_portfolio_and_payloads_non_vacuous_and_tight.2,
   WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.certificates_non_vacuous_and_tight⟩

#print axioms panToTarget_noStubLoc6_non_vacuous_and_tight
#print axioms panToTarget_user_noStubLoc6_non_vacuous_and_tight
#print axioms compact_len_cases_and_compact_zero_iff_non_vacuous_and_tight
#print axioms ext_zero_rejected_non_vacuous_and_tight
#print axioms walk_bound_decoded_non_vacuous_and_tight
#print axioms expansion_traps_non_vacuous_and_tight
#print axioms heap_allocation_non_vacuous_and_tight
#print axioms heap_nodes_non_vacuous_and_tight
#print axioms heap_rates_non_vacuous_and_tight
#print axioms memo_non_vacuous_and_tight
#print axioms fifty_six_portfolio_and_payloads_non_vacuous_and_tight
#print axioms no_loc_value_6_witness_dag_and_fifty_six_budget_master_non_vacuous_and_tight

end InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster
