import InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption
import InitECandidate.Solver.WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster
import InitECandidate.Solver.SelfContainedWarmAccessSetAndDistinctDeleteSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_127. Shared absorption across eleven tables and the exact sorted union
of W5_125's forty-four budgets with four new tiers. Finite certificates are
conditional on a semantic base certificate; arithmetic alone is no clock proof.
Only the three requested Solver modules are imported. -/
namespace InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (M S kPanElevenTablesShared)
open _root_.InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (coupledCost witness feasible)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt certificate_lift_non_vacuous_and_tight)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

def elevenTablesSharedSlope3UnrolledK : Nat := 3 * 156_088_992_805 + 9_232
def elevenTablesSharedSlope3K : Nat := 3 * 156_088_992_805 + 23_032
def elevenTablesSharedSlope5UnrolledK : Nat := 5 * 156_088_992_805 + 9_232
def elevenTablesSharedSlope5K : Nat := 5 * 156_088_992_805 + 23_032

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
  elevenTablesSharedSlope3UnrolledK,
  elevenTablesSharedSlope3K,
  479679833456,
  479679847256,
  WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3UnrolledK,
  WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope3K,
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
  elevenTablesSharedSlope5UnrolledK,
  elevenTablesSharedSlope5K,
  785125408508,
  799466382872,
  799466396672,
  WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5UnrolledK,
  WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.warmSetsSlope5K,
  810291208508,
  816696823280,
  816696837080,
  857384015252
]

/-- Storage, deletion and probe regimes consume a single shared budget. -/
theorem shared_absorption_non_vacuous_and_tight (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    blk + 13 * loc + t2 + t3 + t4 ≤ 151929428571 :=
  GuestElevenTablesSharedBudgetAbsorption.shared_absorption B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4

/-- Attainable storage corner and exact integer envelope. -/
theorem shared_corner_non_vacuous_and_tight :
    40 * 100000000000 ≤ S * S ∧ 84 * 3994571428 ≤ M * S ∧
    (21 * S * S + 130 * M * S) / 840 = 151929428571 :=
  GuestElevenTablesSharedBudgetAbsorption.shared_tight

theorem kPan_val_non_vacuous_and_tight :
    kPanElevenTablesShared = 156088992805 ∧
    GuestElevenTablesAndWarmAddressProbeBound.kPanElevenTables - kPanElevenTablesShared = 11342996533 :=
  GuestElevenTablesSharedBudgetAbsorption.kPan_val

/-- The feasible twelve-transaction witness brackets the shared envelope. -/
theorem bracket_non_vacuous_and_tight :
    feasible witness ∧ coupledCost witness = 155688931265 ∧
    coupledCost witness ≤ kPanElevenTablesShared ∧
    kPanElevenTablesShared - coupledCost witness = 400061540 ∧
    400061540 * 10000 < 26 * 156088992805 ∧
    400061540 * 10000 < 26 * 155688931265 :=
  ⟨GuestElevenTablesSharedBudgetAbsorption.lower_witness.1,
   GuestElevenTablesSharedBudgetAbsorption.lower_witness.2,
   GuestElevenTablesSharedBudgetAbsorption.bracket.1,
   GuestElevenTablesSharedBudgetAbsorption.bracket.2,
   GuestElevenTablesSharedBudgetAbsorption.bracket_rel, by decide⟩

theorem five_margin_non_vacuous_and_tight :
    5 * kPanElevenTablesShared < yukon ∧
    yukon - 5 * kPanElevenTablesShared = 120274961449 :=
  GuestElevenTablesSharedBudgetAbsorption.five_margin

theorem six_fails_non_vacuous_and_tight :
    yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness :=
  GuestElevenTablesSharedBudgetAbsorption.six_fails

/-- Exact budgets and bootstrap/unrolling offsets, with one-tick minimality. -/
theorem target_values_non_vacuous_and_tight :
    elevenTablesSharedSlope3UnrolledK = 468266987647 ∧
    elevenTablesSharedSlope3K = 468267001447 ∧
    elevenTablesSharedSlope5UnrolledK = 780444973257 ∧
    elevenTablesSharedSlope5K = 780444987057 ∧
    elevenTablesSharedSlope3K - elevenTablesSharedSlope3UnrolledK = 13800 ∧
    elevenTablesSharedSlope5K - elevenTablesSharedSlope5UnrolledK = 13800 ∧
    ¬ (3 * kPanElevenTablesShared + 9232 ≤ elevenTablesSharedSlope3UnrolledK - 1) ∧
    ¬ (5 * kPanElevenTablesShared + 23032 ≤ elevenTablesSharedSlope5K - 1) := by decide

/-- The original forty-four budgets are retained exactly. -/
theorem portfolio_union_non_vacuous_and_tight (K : Nat) :
    K ∈ portfolio ↔ K ∈ WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.portfolio ∨
      K ∈ [elevenTablesSharedSlope3UnrolledK, elevenTablesSharedSlope3K,
        elevenTablesSharedSlope5UnrolledK, elevenTablesSharedSlope5K] := by
  simp only [portfolio, WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.portfolio,
    List.mem_cons, List.not_mem_nil, or_false]
  simp only [or_assoc, or_left_comm, or_comm]

theorem portfolio_shape_non_vacuous_and_tight :
    portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474 := by decide

/-- Conditional certificates for all forty-eight tiers. -/
theorem forty_eight_certified_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ K ∈ portfolio, K < 900719925474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
  refine ⟨portfolio_shape_non_vacuous_and_tight.1,
    portfolio_shape_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  have hb := portfolio_shape_non_vacuous_and_tight.2.2 K hK
  exact ⟨hb.2, certificate_lift_non_vacuous_and_tight _ K hb.1 cert⟩

/-- Explicit submission identity and certificate at the selected tier. -/
theorem submission_certificate_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) (K : Nat) (hK : K ∈ portfolio)
    (submission : InitE.Submission) (hs : submission = baselineWithFiniteK K) :
    K < 900719925474 ∧ InitE.Certificate submission (.finite K) := by
  subst submission
  exact (forty_eight_certified_non_vacuous_and_tight cert).2.2 K hK

/-- Warm rollback from the self-contained synthesis, distinct-delete payment,
shared eleven-table envelope, feasible witness and the forty-eight certificates. -/
theorem integrated_master_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) (n k d p q w : Nat)
    (H2 : p + GuestDistinctDeleteOrCallCycleSixSlope.cycleUnits * q ≤ w) :
    (GuestWarmAccessSetAndRollbackBound.truncDels
      (GuestWarmAccessSetAndRollbackBound.warmN (GuestWarmAccessSetAndRollbackBound.enter n) k) = k ∧
     (GuestWarmAccessSetAndRollbackBound.warmN (GuestWarmAccessSetAndRollbackBound.enter n) k).size -
      GuestWarmAccessSetAndRollbackBound.truncDels
        (GuestWarmAccessSetAndRollbackBound.warmN (GuestWarmAccessSetAndRollbackBound.enter n) k) = n) ∧
    (8 * d * p + 13 * d * q ≤ 8 * d * w ∧ 8 * d * w + 13 * d * 0 = 8 * d * w) ∧
    (feasible witness ∧ coupledCost witness = 155688931265) ∧
    (kPanElevenTablesShared = 156088992805 ∧
      yukon - 5 * kPanElevenTablesShared = 120274961449) ∧
    (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, K < 900719925474 ∧
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  have hw := SelfContainedWarmAccessSetAndDistinctDeleteSynth.guest_warm_access_set_and_rollback_bound_closure_non_vacuous_and_tight
    n k 0 0 (by decide) (by decide)
  have hd := WarmAccessSetAndDistinctDeleteFortyFourBudgetMaster.distinct_delete_non_vacuous_and_tight d p q w H2
  exact ⟨⟨hw.1, hw.2.1⟩, hd.2.2,
    GuestElevenTablesSharedBudgetAbsorption.lower_witness,
    ⟨kPan_val_non_vacuous_and_tight.1, five_margin_non_vacuous_and_tight.2⟩,
    forty_eight_certified_non_vacuous_and_tight cert⟩

#print axioms shared_absorption_non_vacuous_and_tight
#print axioms shared_corner_non_vacuous_and_tight
#print axioms kPan_val_non_vacuous_and_tight
#print axioms bracket_non_vacuous_and_tight
#print axioms five_margin_non_vacuous_and_tight
#print axioms six_fails_non_vacuous_and_tight
#print axioms target_values_non_vacuous_and_tight
#print axioms portfolio_union_non_vacuous_and_tight
#print axioms portfolio_shape_non_vacuous_and_tight
#print axioms forty_eight_certified_non_vacuous_and_tight
#print axioms submission_certificate_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster
