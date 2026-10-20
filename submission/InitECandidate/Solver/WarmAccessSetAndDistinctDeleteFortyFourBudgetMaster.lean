import InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound
import InitECandidate.Solver.DistinctDeleteCycleAndCoupledRevertMaster
import InitECandidate.Solver.SelfContainedCoupledRevertTxCapAndDisjointTablesSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_125. Warm tables ev+168 / ev+176 and rollback_child_access extend
 the forty-budget synthesis. The requested target offsets are 23,032 and
 23,032 - 13,800; they are explicit here. Certificates retain a semantic
 base-certificate premise: arithmetic envelopes alone imply no execution clock.
 No direct Proofs.Bounded imports. -/
namespace InitECandidate.Solver.WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt certificate_lift_non_vacuous_and_tight)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- Four new target budgets, with the requested explicit bootstrap offset. -/
def warmSetsSlope3UnrolledK : Nat := 3 * kPanWarmSets + 23032 - 13800
def warmSetsSlope3K : Nat := 3 * kPanWarmSets + 23032
def warmSetsSlope5UnrolledK : Nat := 5 * kPanWarmSets + 23032 - 13800
def warmSetsSlope5K : Nat := 5 * kPanWarmSets + 23032

/-- Sorted union of the old forty budgets and the four warm-set budgets. -/
def portfolio : List Nat := [
  1212035192,
  2038701869,
  11029669988,
  11029683788,
  19392692330,
  22059330644,
  22059344444,
  32791963724,
  87829684748,
  121459456007,
  122620608536,
  214346021162,
  242918888882,
  296693001548,
  387840417875,
  392562715820,
  405145615820,
  408348416306,
  408348430106,
  428692019192,
  459244490549,
  479679833456,
  479679847256,
  warmSetsSlope3UnrolledK,
  warmSetsSlope3K,
  485837754632,
  500060306876,
  540194146716,
  593385979964,
  610978715738,
  610978730738,
  675242677612,
  677645382458,
  677645397458,
  775680812618,
  785125408508,
  799466382872,
  799466396672,
  warmSetsSlope5UnrolledK,
  warmSetsSlope5K,
  810291208508,
  816696823280,
  816696837080,
  857384015252
]

/-- Rollback truncates both independently shared tables to their parent marks. -/
theorem rollback_child_access_non_vacuous_and_tight (na ka ns ks : Nat) :
    truncDels (warmN (enter na) ka) = ka ∧
    (warmN (enter na) ka).size - truncDels (warmN (enter na) ka) = na ∧
    truncDels (warmN (enter ns) ks) = ks ∧
    (warmN (enter ns) ks).size - truncDels (warmN (enter ns) ks) = ns :=
  ⟨trunc_exact na ka, trunc_keeps_parent na ka,
   trunc_exact ns ks, trunc_keeps_parent ns ks⟩

/-- Address cardinality and delete cost, including their attainable corners. -/
theorem address_bounds_non_vacuous_and_tight (a n : Nat)
    (ha : 30 * a ≤ 167772) (hn : 30 * n ≤ 2000000) :
    a + 19 ≤ 5611 ∧ truncTicks (a + 19) n ≤ 1870314630 ∧
    30 * 5592 ≤ 167772 ∧ 167772 < 30 * 5593 ∧
    truncTicks 5611 66666 = 1870314630 :=
  ⟨addr_set_tx a ha, addr_trunc_le _ n (addr_set_tx a ha) (addr_dels_block n hn),
   addr_set_tx_tight.1, addr_set_tx_tight.2, addr_trunc_tight⟩

/-- Storage truncation stays absorbed; only the address term is added. -/
theorem warm_envelope_non_vacuous_and_tight :
    GuestAccessListAndCallStackDominance.kPanAccessCall =
      136116135658 + 19972857140 + 3804281910 ∧
    kPanWarmSets = 161763589338 ∧
    5 * kPanWarmSets < yukon ∧ yukon - 5 * kPanWarmSets = 91901978784 ∧
    yukon < 6 * kPanWarmSets :=
  ⟨storage_trunc_in_access, kPanWarmSets_val, slopes⟩

theorem target_values_non_vacuous_and_tight :
    warmSetsSlope3UnrolledK = 485290777246 ∧
    warmSetsSlope3K = 485290791046 ∧
    warmSetsSlope5UnrolledK = 808817955922 ∧
    warmSetsSlope5K = 808817969722 ∧
    warmSetsSlope3K - warmSetsSlope3UnrolledK = 13800 ∧
    warmSetsSlope5K - warmSetsSlope5UnrolledK = 13800 ∧
    warmSetsSlope5K < 900719925474 := by decide

/-- Exact union: no old budget is lost and no other budget is introduced. -/
theorem portfolio_union_non_vacuous_and_tight (K : Nat) :
    K ∈ portfolio ↔ K ∈ DistinctDeleteCycleAndCoupledRevertMaster.portfolio ∨
      K ∈ [warmSetsSlope3UnrolledK, warmSetsSlope3K,
        warmSetsSlope5UnrolledK, warmSetsSlope5K] := by
  rw [DistinctDeleteCycleAndCoupledRevertMaster.self_contained_alignment_non_vacuous_and_tight.1]
  simp only [portfolio, SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio,
    List.mem_cons, List.not_mem_nil, or_false]
  simp only [or_assoc, or_left_comm, or_comm]

/-- Cardinality, strict order, semantic lifting floor, and Yukon ceiling. -/
theorem portfolio_shape_non_vacuous_and_tight :
    portfolio.length = 44 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474 := by decide

/-- Conditional finite certificates for every member of the extended portfolio. -/
theorem forty_four_certified_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    portfolio.length = 44 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ K ∈ portfolio, K < 900719925474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
  refine ⟨portfolio_shape_non_vacuous_and_tight.1,
    portfolio_shape_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  have hb := portfolio_shape_non_vacuous_and_tight.2.2 K hK
  exact ⟨hb.2, certificate_lift_non_vacuous_and_tight _ K hb.1 cert⟩

/-- Submission identity remains explicit in the final certificate. -/
theorem submission_certificate_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) (K : Nat) (hK : K ∈ portfolio)
    (submission : InitE.Submission) (hs : submission = baselineWithFiniteK K) :
    K < 900719925474 ∧ InitE.Certificate submission (.finite K) := by
  subst submission
  exact (forty_four_certified_non_vacuous_and_tight cert).2.2 K hK

open _root_.InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes
open _root_.InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening hiding S slopes
open _root_.InitECandidate.Solver.GuestAccessListAndCallStackDominance (kPanAccessCall)
open _root_.InitECandidate.Solver.GuestStateRestoreCoupledTightening (kPanStateRestoreCoupled)

/-- Full self-contained coupled revert and disjoint-table audit. -/
theorem coupled_disjoint_audit_non_vacuous_and_tight
    (s : Sizes) (d_t w_t db dx D W : Nat)
    (htx : 21 * d_t + w_t ≤ M)
    (hp : db + dx ≤ D) (hgas : 21 * D + W ≤ 2000000) :
    (21 * 7989 ≤ M ∧ M < 21 * 7990) ∧
    d_t ≤ 7989 ∧
    (21 * 4114 + 81378 = M ∧ 21 * 3783 + 75065 ≤ M ∧
      (witness.map (fun p => 21 * p.1 + p.2)).sum = GuestCoupledRevertAndTxCapTightening.S) ∧
    feasible witness ∧
    ((witness.map Prod.fst).sum = 49037 ∧ (witness.map Prod.snd).sum = 970223 ∧
      (witness.map (fun p => p.1 * p.2)).sum = 3966650907) ∧
    coupledCost witness = 155688931265 ∧
    (6 * 150119987578 < yukon ∧ yukon ≤ 6 * 150119987579) ∧
    (∃ l, feasible l ∧ yukon < 6 * coupledCost l) ∧
    coupledCost witness ≤ kPanAccessCall ∧
    (kPanCoupledRevertTxCap = 159893274708 ∧ 5 * kPanCoupledRevertTxCap < yukon ∧
      yukon < 6 * kPanCoupledRevertTxCap) ∧
    kPanCoupledRevertTxCap = kPanDisjointTables ∧
    kPanCoupledRevertTxCap = kPanStateRestoreCoupled ∧
    ((endTx s).db + (endTx s).dx = s.db + s.dx ∧
      (endTx s).dx = 0 ∧
      (dirty s).db + (dirty s).dx = s.db + s.dx + 1 ∧
      21 * (db + dx) + W ≤ 2000000 ∧
      2 * db + 13 * dx ≤ 13 * (db + dx) ∧
      cycleTicks db dx ≤ 13 * D ∧
      cycleTicks 0 D = 13 * D ∧
      cycleTicks D 0 = 2 * D ∧
      cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) ∧
      kPanDisjointTables = 159893274708 ∧
      kPanDisjointTables = kPanStateRestoreCoupled ∧
      kPanDisjointTables = kPanAccessCall ∧
      (5 * kPanDisjointTables < yukon ∧ yukon < 6 * kPanDisjointTables ∧
        yukon - 5 * kPanDisjointTables = 101253551934)) := by
  exact SelfContainedCoupledRevertTxCapAndDisjointTablesSynth.guest_coupled_revert_and_tx_cap_tightening_complete_audit_non_vacuous_and_tight s d_t w_t db dx D W htx hp hgas

/-- Distinct deletes require H2 for the restored six-slope estimate. -/
theorem distinct_delete_non_vacuous_and_tight (d p q w : Nat)
    (H2 : p + GuestDistinctDeleteOrCallCycleSixSlope.cycleUnits * q ≤ w) :
    GuestDistinctDeleteOrCallCycleSixSlope.journalFlags [] [d, d] = [false, true] ∧
    (GuestDistinctDeleteOrCallCycleSixSlope.dels [] [1, 1, 1, 2, 2] = 2 ∧
      GuestDistinctDeleteOrCallCycleSixSlope.dels [1] [1, 1] = 0) ∧
    (8 * d * p + 13 * d * q ≤ 8 * d * w ∧
      8 * d * w + 13 * d * 0 = 8 * d * w) :=
  ⟨DistinctDeleteCycleAndCoupledRevertMaster.repeat_no_delete_non_vacuous_and_tight d,
   DistinctDeleteCycleAndCoupledRevertMaster.dels_distinct_non_vacuous_and_tight,
   DistinctDeleteCycleAndCoupledRevertMaster.revert_le_tight_non_vacuous_and_tight d p q w H2⟩

/-- Coupled warm rollback, distinct-delete payment, per-tx cap, unconditional
six-slope counterexample and the forty-four submission certificates. -/
theorem integrated_master_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) (n k d p q w d_t w_t : Nat)
    (H2 : p + GuestDistinctDeleteOrCallCycleSixSlope.cycleUnits * q ≤ w)
    (htx : 21 * d_t + w_t ≤ M) :
    (truncDels (warmN (enter n) k) = k ∧
      (warmN (enter n) k).size - truncDels (warmN (enter n) k) = n) ∧
    (kPanWarmSets = 161763589338 ∧ 5 * kPanWarmSets < yukon ∧
      yukon - 5 * kPanWarmSets = 91901978784) ∧
    (8 * d * p + 13 * d * q ≤ 8 * d * w ∧
      8 * d * w + 13 * d * 0 = 8 * d * w) ∧
    d_t ≤ 7989 ∧
    (feasible witness ∧ coupledCost witness = 155688931265 ∧
      yukon < 6 * coupledCost witness ∧
      ∃ l, feasible l ∧ yukon < 6 * coupledCost l) ∧
    (portfolio.length = 44 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, K < 900719925474 ∧
        ∃ submission : InitE.Submission, submission = baselineWithFiniteK K ∧
          InitE.Certificate submission (.finite K)) := by
  refine ⟨⟨trunc_exact n k, trunc_keeps_parent n k⟩,
    ⟨kPanWarmSets_val, GuestWarmAccessSetAndRollbackBound.slopes.1,
      GuestWarmAccessSetAndRollbackBound.slopes.2.1⟩,
    DistinctDeleteCycleAndCoupledRevertMaster.revert_le_tight_non_vacuous_and_tight d p q w H2,
    dx_le d_t w_t htx,
    DistinctDeleteCycleAndCoupledRevertMaster.no_six_restore_non_vacuous_and_tight,
    portfolio_shape_non_vacuous_and_tight.1, portfolio_shape_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  have hc := (forty_four_certified_non_vacuous_and_tight cert).2.2 K hK
  exact ⟨hc.1, baselineWithFiniteK K, rfl, hc.2⟩

#print axioms rollback_child_access_non_vacuous_and_tight
#print axioms address_bounds_non_vacuous_and_tight
#print axioms warm_envelope_non_vacuous_and_tight
#print axioms target_values_non_vacuous_and_tight
#print axioms portfolio_union_non_vacuous_and_tight
#print axioms portfolio_shape_non_vacuous_and_tight
#print axioms forty_four_certified_non_vacuous_and_tight
#print axioms submission_certificate_non_vacuous_and_tight
#print axioms coupled_disjoint_audit_non_vacuous_and_tight
#print axioms distinct_delete_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster
