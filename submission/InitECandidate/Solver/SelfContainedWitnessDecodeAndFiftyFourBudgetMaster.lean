import InitECandidate.Solver.SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth
import InitECandidate.Solver.WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge
import InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_157: decoded witness validation, unconditional compiler safety and 54 budgets.
The decoded-walk contract explicitly assumes at most 64 consumed nibbles.
Finite semantic certificates remain conditional on the base certificate.
-/
namespace InitECandidate.Solver.SelfContainedWitnessDecodeAndFiftyFourBudgetMaster

open InitECandidate.Solver
open InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit
open InitECandidate.Solver.GuestMptTraversalAndStateRootBound (Step advance)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)


abbrev portfolio := MptTraversalStateRootAndFiftyFourBudgetMaster.portfolio
abbrev fiftyFourClaims := MptTraversalStateRootAndFiftyFourBudgetMaster.fiftyFourClaims

def CompactContract : Prop :=
  (∀ n : Nat, 1 ≤ n → compactLen n 0 = 2 * n - 2 ∧ compactLen n 1 = 2 * n - 1) ∧
  (∀ n odd : Nat, 1 ≤ n → odd ≤ 1 → (compactLen n odd = 0 ↔ n = 1 ∧ odd = 0)) ∧
  (compactLen 1 0 = 0 ∧ compactLen 1 1 = 1 ∧
    compactLen 33 0 = 64 ∧ compactLen 32 1 = 63)

theorem compact_len_cases_zero_iff_full_key_non_vacuous_and_tight : CompactContract := by
  have h := SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.compact_to_nibbles_and_extension_rejection_non_vacuous_and_tight 3 1
  exact ⟨h.1, h.2.1, h.2.2.1⟩

def ExtensionContract : Prop :=
  (∀ ck : Nat, extAccepted 0 ck = false) ∧
  (∀ l : Nat, extAccepted l 2 = false ∧ extAccepted l 1 = false) ∧
  (∀ l ck : Nat, extAccepted l ck = true → 1 ≤ advance (.ext l)) ∧
  (extAccepted 1 3 = true ∧ extAccepted 1 0 = true ∧ advance (.ext 1) = 1)

theorem ext_zero_child_rejected_and_accepted_advances_non_vacuous_and_tight :
    ExtensionContract :=
  ⟨fun ck => (WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge.ext_zero_and_child_rejected_non_vacuous_and_tight 1 ck).1,
   fun l => (WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge.ext_zero_and_child_rejected_non_vacuous_and_tight l 3).2,
   accepted_advances, by decide⟩

def DecodedWalkContract : Prop :=
  (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
    ((l.map Step.ext).map advance).sum ≤ 64 → l.length ≤ 64 ∧ l.length + 1 ≤ 65) ∧
  ((List.replicate 64 1).length + 1 = 65 ∧
    (((List.replicate 64 1).map Step.ext).map advance).sum = 64)

theorem walk_bound_decoded_non_vacuous_and_tight : DecodedWalkContract :=
  ⟨(SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth.decoded_trie_walk_bound_and_witness_heap_expansion_non_vacuous_and_tight).1,
   by decide⟩

def HeapContract : Prop :=
  (33806089496 - 2713714688) / 56 = 555220978 ∧
  ((List.range 7).foldl (fun a i => a + 16 ^ i) 0 = 17895697 ∧
    17895697 * 176 + 16 ^ 7 * 64 = 20329511856 ∧
    20329511856 ≤ 33806089496 - 2713714688) ∧
  33806089496 - 2713714688 < 16 ^ 8 * 64 ∧
  (17895697 + 16 ^ 7 = 286331153 ∧ 8 * 530 < 4300)

theorem heap_nodes_and_expansion_traps_non_vacuous_and_tight : HeapContract :=
  WitnessDecodeExtensionNibbleAndFiftyTwoBudgetBridge.heap_nodes_expansion_and_ratio_non_vacuous_and_tight

theorem cold_access_totals_non_vacuous_and_tight : MptTraversalStateRootAndFiftyFourBudgetMaster.AccessContract :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.accesses_non_vacuous_and_tight

theorem compute_state_root_totals_non_vacuous_and_tight : MptTraversalStateRootAndFiftyFourBudgetMaster.RootContract :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.state_root_non_vacuous_and_tight

/-- No additional safety premise on the source program. -/
theorem panToTarget_noStubJump_non_vacuous_and_tight : MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.panToTarget_noStubJump_non_vacuous_and_tight

/-- Every user section is safe, without a source-program safety premise. -/
theorem panToTarget_user_noStubJump_non_vacuous_and_tight : MptTraversalStateRootAndFiftyFourBudgetMaster.PanUserSafe :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.panToTarget_user_noStubJump_non_vacuous_and_tight

theorem fifty_four_budget_portfolio_non_vacuous_and_tight : MptTraversalStateRootAndFiftyFourBudgetMaster.FiftyFourShape :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.portfolio_non_vacuous_and_tight

theorem fifty_four_claim_payloads_non_vacuous_and_tight : MptTraversalStateRootAndFiftyFourBudgetMaster.ClaimPayloads :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.payloads_non_vacuous_and_tight

theorem fifty_four_finite_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K) :=
  MptTraversalStateRootAndFiftyFourBudgetMaster.certificates_non_vacuous_and_tight cert

/-- Arithmetic and compiler safety are unconditional; only semantic lifting
requires the base certificate. The previous 52 tiers are preserved as a prefix. -/
theorem self_contained_witness_decode_and_fifty_four_budget_master_non_vacuous_and_tight :
    CompactContract ∧ ExtensionContract ∧ DecodedWalkContract ∧ HeapContract ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.WalkContract ∧ MptTraversalStateRootAndFiftyFourBudgetMaster.AccessContract ∧ MptTraversalStateRootAndFiftyFourBudgetMaster.RootContract ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.WitnessLinearContract ∧ MptTraversalStateRootAndFiftyFourBudgetMaster.CoupledJournalContract ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.FrontendSafe ∧ MptTraversalStateRootAndFiftyFourBudgetMaster.PanLabSafe ∧ MptTraversalStateRootAndFiftyFourBudgetMaster.PanTargetSafe ∧ MptTraversalStateRootAndFiftyFourBudgetMaster.PanUserSafe ∧
    MptTraversalStateRootAndFiftyFourBudgetMaster.FiftyFourShape ∧ MptTraversalStateRootAndFiftyFourBudgetMaster.ClaimPayloads ∧
    (CertificateAt 1212035192 →
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨compact_len_cases_zero_iff_full_key_non_vacuous_and_tight,
   ext_zero_child_rejected_and_accepted_advances_non_vacuous_and_tight,
   walk_bound_decoded_non_vacuous_and_tight,
   heap_nodes_and_expansion_traps_non_vacuous_and_tight,
   MptTraversalStateRootAndFiftyFourBudgetMaster.traversal_non_vacuous_and_tight,
   cold_access_totals_non_vacuous_and_tight,
   compute_state_root_totals_non_vacuous_and_tight,
   MptTraversalStateRootAndFiftyFourBudgetMaster.witness_and_linear_non_vacuous_and_tight,
   MptTraversalStateRootAndFiftyFourBudgetMaster.coupled_journal_non_vacuous_and_tight,
   InitECandidate.Solver.SelfContainedTransientStorageJournalAndFiftyBudgetSynth.unconditional_pan_to_word_and_word_to_word_no_stub_call_non_vacuous_and_tight,
   MptTraversalStateRootAndFiftyFourBudgetMaster.panToLab_lines_non_vacuous_and_tight,
   panToTarget_noStubJump_non_vacuous_and_tight,
   panToTarget_user_noStubJump_non_vacuous_and_tight,
   fifty_four_budget_portfolio_non_vacuous_and_tight,
   fifty_four_claim_payloads_non_vacuous_and_tight,
   fifty_four_finite_certificates_non_vacuous_and_tight⟩

#print axioms compact_len_cases_zero_iff_full_key_non_vacuous_and_tight
#print axioms ext_zero_child_rejected_and_accepted_advances_non_vacuous_and_tight
#print axioms walk_bound_decoded_non_vacuous_and_tight
#print axioms heap_nodes_and_expansion_traps_non_vacuous_and_tight
#print axioms cold_access_totals_non_vacuous_and_tight
#print axioms compute_state_root_totals_non_vacuous_and_tight
#print axioms panToTarget_noStubJump_non_vacuous_and_tight
#print axioms panToTarget_user_noStubJump_non_vacuous_and_tight
#print axioms fifty_four_budget_portfolio_non_vacuous_and_tight
#print axioms fifty_four_claim_payloads_non_vacuous_and_tight
#print axioms fifty_four_finite_certificates_non_vacuous_and_tight
#print axioms self_contained_witness_decode_and_fifty_four_budget_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWitnessDecodeAndFiftyFourBudgetMaster
