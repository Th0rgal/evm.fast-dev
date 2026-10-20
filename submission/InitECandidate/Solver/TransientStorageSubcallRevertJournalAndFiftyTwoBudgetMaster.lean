import InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption
import InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis
import InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_144. Integration of the hand-transcribed transient tick model, hypothetical
run-cap absorption, shared gas coupling and 52 finite tiers. No semantic clock
certificate is inferred from this arithmetic: finite certificates explicitly
retain the base-certificate obligation. The current Guest has no such run cap. -/
namespace InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (buildTicks)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)


/-- Two explicit one-tick relaxations preserve the preceding fifty tiers. -/
def portfolio : List Nat := _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.portfolio ++ [857384015255, 857384015256]

def fiftyTwoClaims : List (Nat × String) := _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.fiftyClaims ++
  [(857384015255, "{\"K\":857384015255}"),
   (857384015256, "{\"K\":857384015256}")]

def FiftyTwoShape : Prop :=
  portfolio.length = 52 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
  portfolio.take 50 = _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.portfolio

def ClaimPayloads : Prop :=
  fiftyTwoClaims.length = 52 ∧ fiftyTwoClaims.map Prod.fst = portfolio ∧
  ∀ e ∈ fiftyTwoClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true

/-- 1. Splitting cannot increase the quadratic model; the empty/single chunk
bounds are attainable and two nontrivial chunks give a strict loss. -/
theorem split_non_vacuous_and_tight (l : List Nat) :
    (l.map buildTicks).sum ≤ buildTicks l.sum ∧
    buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30 ∧
    buildTicks 2 + buildTicks 2 < buildTicks 4 ∧
    ([158162].map buildTicks).sum = buildTicks ([158162].sum) := by
  refine ⟨_root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.split_le l, _root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.split_strict.1, _root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.split_strict.2, ?_, ?_⟩
  · decide
  · simp

/-- 2. Exact end-of-transaction rollback and halving witnesses. -/
theorem revert_and_half_non_vacuous_and_tight :
    2 * buildTicks 158162 = 125075300410 ∧
    2 * buildTicks 79081 = 31268627400 ∧ buildTicks 158162 = 62537650205 :=
  ⟨_root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.tx_worst_revert, _root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.half_split⟩

/-- 3. Both run-cap thresholds, including the first excluded integer. -/
theorem thresholds_non_vacuous_and_tight (L : Nat) :
    (10 * L ≤ 50000 ↔ L ≤ 5000) ∧ (5 * L ≤ 50000 ↔ L ≤ 10000) ∧
    (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧
     5 * 10000 = 50000 ∧ 50000 < 5 * 10001) :=
  ⟨_root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.lmax_revert L, _root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.lmax_norevert L, _root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.lmax_sharp⟩

/-- 4. Universally quantified feasible cap regime, with an attained nonzero endpoint.
The enclosing eleven-table budget passes fivefold, but not sixfold. -/
theorem cap_absorption_non_vacuous_and_tight :
    (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
      40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
    (10 * 5000 * 2000000 = 100000000000) ∧
    100000000000 ≤ 156088992805 ∧
    5 * 156088992805 < yukon ∧ yukon < 6 * 156088992805 ∧ 5000 < 158162 := by
  exact ⟨_root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.absorbed_with_cap, by decide, by decide,
    _root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.guest_vs_cap.2, by decide, _root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.guest_vs_cap.1⟩

/-- 5. Gas is measured in 100-gas units. The shared 200M budget is convex,
not an independent 200M allowance for each regime; its slope bound is attained. -/
theorem coupled_non_vacuous_and_tight :
    (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
      t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
    100 * 2000000 = 200000000 ∧
    373022 * 2000000 + 373022 * 0 = 746044000000 ∧
    11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
    746044000000 - 740946409660 = 5097590340 :=
  ⟨_root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.coupled_le, by decide, by decide, _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.bracket⟩

/-- 6. Exact Yukon headroom with linear costs and the twofold obstruction. -/
theorem yukon_margin_non_vacuous_and_tight :
    (746044000000 + 4159564234 < yukon ∧
      yukon - (746044000000 + 4159564234) = 150516361240 ∧
      yukon < 2 * (740946409660 + 4159564234)) ∧
    746044000000 < 740946409660 + 156088992805 :=
  ⟨_root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.slopes, _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.coupled_vs_additive⟩

/-- 7. Each journal entry is undone once; all absent entries attain the cap. -/
theorem journal_non_vacuous_and_tight :
    (∀ j : List Bool, j.length ≤ 524288 → _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j ≤ 524288) ∧
    _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels (List.replicate 524288 false) = 524288 ∧
    (_root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels [false, true, false] = 2 ∧ _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels [true, true] = 0) ∧
    ((1 + 1 : Nat) = 2 ∧ (1 + 1 + 1 : Nat) = 3) := by
  refine ⟨_root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restore_once, ?_, _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.journal_actions, _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.step_ticks⟩
  exact List.count_replicate_self

/-- 8. Exact integer slope and the lower storage slope. -/
theorem slope_non_vacuous_and_tight :
    (∀ k : Nat, k ≤ 158162 → 100 * buildTicks k ≤ 373022 * (106 * k)) ∧
    ¬ (250 * (158162 - 1) ≤ 106 * 373021) ∧
    (2000000 / 20 / 2 + 13 * 167772 / 84 + 1 = 75965 ∧ 75965 < 373022) :=
  ⟨_root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.tstore_per_gas, _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.tstore_slope_tight, _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.storage_slope⟩

/-- 9. The original transaction, packing, storage-envelope and obstruction contracts. -/
theorem previous_analysis_non_vacuous_and_tight :
    _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.KeyCap ∧ _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.PackingAndBuild ∧ _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.BlockCosts ∧
    _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.OneSlopeMargin ∧ _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.TransientObstruction ∧ _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.RemainingTables :=
  ⟨_root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.key_cap_non_vacuous_and_tight, _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.packing_and_tx_build_non_vacuous_and_tight,
    _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.block_and_revert_non_vacuous_and_tight, _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.one_slope_margin_non_vacuous_and_tight,
    _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.transient_obstruction_non_vacuous_and_tight, GuestTransientStorageAndRemainingTablesAudit.remaining_absorbed⟩

/-- 10. Exactly 52 strictly increasing budgets, preserving all preceding tiers. -/
theorem fifty_two_shape_non_vacuous_and_tight : FiftyTwoShape := by
  unfold FiftyTwoShape
  decide

/-- 11. Explicit finite JSON claims for exactly the same 52 budgets. -/
theorem fifty_two_payloads_non_vacuous_and_tight : ClaimPayloads := by
  unfold ClaimPayloads
  decide

/-- 12. Semantic lifting retains the explicit base certificate. All arithmetic
regimes above have concrete witnesses independently of this semantic obligation. -/
theorem integrated_master_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    FiftyTwoShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (∀ l : List Nat, (l.map buildTicks).sum ≤ buildTicks l.sum) ∧
    (∀ j : List Bool, j.length ≤ 524288 → _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j ≤ 524288) ∧
    (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
      t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
    (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
      40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
    _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.KeyCap ∧ _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.PackingAndBuild ∧ _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.BlockCosts ∧
    _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.OneSlopeMargin ∧ _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.TransientObstruction ∧ _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.RemainingTables := by
  refine ⟨fifty_two_shape_non_vacuous_and_tight, fifty_two_payloads_non_vacuous_and_tight,
    ?_, _root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.split_le, _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restore_once, _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.coupled_le,
    _root_.InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption.absorbed_with_cap, previous_analysis_non_vacuous_and_tight⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (fifty_two_shape_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms split_non_vacuous_and_tight
#print axioms revert_and_half_non_vacuous_and_tight
#print axioms thresholds_non_vacuous_and_tight
#print axioms cap_absorption_non_vacuous_and_tight
#print axioms coupled_non_vacuous_and_tight
#print axioms yukon_margin_non_vacuous_and_tight
#print axioms journal_non_vacuous_and_tight
#print axioms slope_non_vacuous_and_tight
#print axioms previous_analysis_non_vacuous_and_tight
#print axioms fifty_two_shape_non_vacuous_and_tight
#print axioms fifty_two_payloads_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster
