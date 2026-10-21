import InitECandidate.Solver.SelfContainedNoLocValue6ExactTicksAndSixtyBudgetMaster
import InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster
import InitECandidate.Solver.FullBlockTransientProbesAndSixtyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_179. User-section control/address safety, coupled ts+64 on a shared
200M gas budget, and 64 finite budgets. Cost bounds are those of the imported
model; execution certificates require the explicit semantic base certificate. -/
namespace InitECandidate.Solver.SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster

open InitECandidate.Solver
open GuestCoupledGasFullBlockWithProbesAndTransientMaster
open _root_.InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster (subHeap subMemo)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev portfolio := FullBlockTransientProbesAndSixtyFourBudgetMaster.portfolio
abbrev sixtyFourClaims := FullBlockTransientProbesAndSixtyFourBudgetMaster.sixtyFourClaims
abbrev SixtyFourShape := FullBlockTransientProbesAndSixtyFourBudgetMaster.SixtyFourShape
abbrev ClaimPayloads := FullBlockTransientProbesAndSixtyFourBudgetMaster.ClaimPayloads

/-- Successful LabToTarget excludes section-6 control and address references
in every user section, with the explicit stub exemption for other sections. -/
theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  ⟨FullBlockTransientProbesAndSixtyFourBudgetMaster.no_loc_value_6_and_exact_ticks_non_vacuous_and_tight.1,
   FullBlockTransientProbesAndSixtyFourBudgetMaster.no_loc_value_6_and_exact_ticks_non_vacuous_and_tight.2.1⟩

/-- Exact singleton ticks and their strict heap margins. -/
theorem exact_ticks_non_vacuous_and_tight :
    SelfContainedNoLocValue6ExactTicksAndSixtyBudgetMaster.ExactTicks :=
  SelfContainedNoLocValue6ExactTicksAndSixtyBudgetMaster.node_ticks_non_vacuous_and_tight

/-- Shared-budget absorption includes both endpoint witnesses; no separate
200M gas allowance is granted to transient storage. -/
theorem general_side_regime_absorption_non_vacuous_and_tight :
    (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
      40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
    (0 + 10 * 5000 * 2000000 = 100000000000) ∧
    (100000000000 + 10 * 5000 * 0 = 100000000000) :=
  ⟨absorbed, by decide, by decide⟩

/-- Zero net ticks through 5000, and the exact first positive excess. -/
theorem zero_net_ticks_non_vacuous_and_tight :
    (∀ L : Nat, excess L = 0 ↔ L ≤ 5000) ∧
    (∀ L : Nat, L ≤ 5000 →
      coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749) ∧
    excess 5001 = 20000000 := by
  refine ⟨?_, block_unchanged, excess_first⟩
  intro L
  unfold excess
  omega

/-- Exact coupled cap, including all smaller runs and the first rejection. -/
theorem one_heap_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled subHeap L < yukon ↔ L ≤ 38786) ∧
    1 * coupled subHeap 38786 < yukon ∧
    yukon ≤ 1 * coupled subHeap 38787 := by
  refine ⟨?_, ?_⟩
  · intro L
    unfold coupled excess subHeap yukon
    omega
  · simpa using lmax1_heap

/-- Exact coupled cap, including all smaller runs and the first rejection. -/
theorem one_memo_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled subMemo L < yukon ↔ L ≤ 40253) ∧
    1 * coupled subMemo 40253 < yukon ∧
    yukon ≤ 1 * coupled subMemo 40254 := by
  refine ⟨?_, ?_⟩
  · intro L
    unfold coupled excess subMemo yukon
    omega
  · simpa using lmax1_memo

/-- Exact coupled cap, including all smaller runs and the first rejection. -/
theorem four_heap_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupled subHeap L < yukon ↔ L ≤ 5009) ∧
    4 * coupled subHeap 5009 < yukon ∧
    yukon ≤ 4 * coupled subHeap 5010 := by
  refine ⟨?_, ?_⟩
  · intro L
    unfold coupled excess subHeap yukon
    omega
  · simpa using lmax4_heap

/-- Exact coupled cap, including all smaller runs and the first rejection. -/
theorem four_memo_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupled subMemo L < yukon ↔ L ≤ 6476) ∧
    4 * coupled subMemo 6476 < yukon ∧
    yukon ≤ 4 * coupled subMemo 6477 := by
  refine ⟨?_, ?_⟩
  · intro L
    unfold coupled excess subMemo yukon
    omega
  · simpa using lmax4_memo

/-- The slope threshold is sharp, and the unsalted attack exceeds both bounds. -/
theorem sharpness_non_vacuous_and_tight :
    (¬ (∀ B U T blk : Nat,
      B + U ≤ GuestExhaustiveHtabInventoryAndSlopeAbsorption.S →
      40 * blk ≤ B * B → T ≤ 50001 * U → blk + T ≤ 100000000000)) ∧
    (40253 < 158162 ∧ yukon < coupled subMemo 158162 ∧
      yukon < coupled subHeap 158162) :=
  ⟨sharp, unsalted_still_fails⟩

/-- Exactly 64 strictly increasing budgets, each strictly below Yukon. -/
theorem portfolio_non_vacuous_and_tight : SixtyFourShape :=
  FullBlockTransientProbesAndSixtyFourBudgetMaster.portfolio_non_vacuous_and_tight

/-- The 64 finite JSON claims match their budgets exactly. -/
theorem payloads_non_vacuous_and_tight : ClaimPayloads :=
  FullBlockTransientProbesAndSixtyFourBudgetMaster.payloads_non_vacuous_and_tight

/-- All finite certificates are conditional on the explicit base certificate;
section safety, exact ticks and portfolio arithmetic are unconditional. -/
theorem certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
    SelfContainedNoLocValue6ExactTicksAndSixtyBudgetMaster.ExactTicks ∧
    SixtyFourShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight.2,
   exact_ticks_non_vacuous_and_tight,
   FullBlockTransientProbesAndSixtyFourBudgetMaster.certificates_non_vacuous_and_tight cert⟩

#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms exact_ticks_non_vacuous_and_tight
#print axioms general_side_regime_absorption_non_vacuous_and_tight
#print axioms zero_net_ticks_non_vacuous_and_tight
#print axioms one_heap_non_vacuous_and_tight
#print axioms one_memo_non_vacuous_and_tight
#print axioms four_heap_non_vacuous_and_tight
#print axioms four_memo_non_vacuous_and_tight
#print axioms sharpness_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms payloads_non_vacuous_and_tight
#print axioms certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster
