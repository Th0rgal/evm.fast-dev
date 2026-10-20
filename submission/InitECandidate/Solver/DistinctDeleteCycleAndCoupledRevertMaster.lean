import InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope
import InitECandidate.Solver.UnifiedDisjointTablesAndCoupledRevertTxCapMaster
import InitECandidate.Solver.SelfContainedDisjointBlockTxAndFortyBudgetSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_123: distinct-delete/call-cycle synthesis. H2 is an explicit payment
hypothesis, not a consequence of EIP-7825. The unconditional coupled witness
still rules out six slopes. Finite certificates retain their semantic base
premise and identify the submission; compiler cleanliness alone gives no clock.
Only the three Solver integration modules above are imported directly. -/
namespace InitECandidate.Solver.DistinctDeleteCycleAndCoupledRevertMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabFilter
open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope
open _root_.InitECandidate.Solver.GuestAccessListAndCallStackDominance (kPanAccessCall)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S)
open _root_.InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes
open _root_.InitECandidate.Solver.GuestStateRestoreCoupledTightening (kPanStateRestoreCoupled)
open _root_.InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (M feasible witness coupledCost kPanCoupledRevertTxCap)
open _root_.InitECandidate.Solver.PanToLabSectionAndStackRemoveClock
open _root_.InitECandidate.Solver.LabToTargetSectionCleanPreservation
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev portfolio := UnifiedDisjointTablesAndCoupledRevertTxCapMaster.portfolio

variable {width : Nat} [NeZero width]

/-- Repeating a key in the same child frame journals it as present. -/
theorem repeat_no_delete_non_vacuous_and_tight (k : Nat) :
    journalFlags [] [k, k] = [false, true] := repeat_no_delete k

/-- Distinct-new-key counting, including the already-present case. -/
theorem dels_distinct_non_vacuous_and_tight :
    dels [] [1, 1, 1, 2, 2] = 2 ∧ dels [1] [1, 1] = 0 := dels_distinct

/-- Both admissible payment mechanisms, in 100-gas units. -/
theorem cycle_units_non_vacuous_and_tight :
    100 + 100 = cycleUnits * 100 ∧ 19 * 100 + 100 = freshUnits * 100 := cycle_units

/-- H2: every delete has two paid units; the all-plain case reaches the envelope. -/
theorem revert_le_tight_non_vacuous_and_tight (d p q w : Nat)
    (H2 : p + cycleUnits * q ≤ w) :
    8 * d * p + 13 * d * q ≤ 8 * d * w ∧
    8 * d * w + 13 * d * 0 = 8 * d * w :=
  ⟨revert_le_tight d p q w H2, revert_tight d w⟩

/-- Restored arithmetic envelope under H2, with its exact gain and slope boundary.
This does not assert an unconditional operational clock. -/
theorem conditional_six_slope_non_vacuous_and_tight (d p q w : Nat)
    (H2 : p + cycleUnits * q ≤ w) :
    8 * d * p + 13 * d * q ≤ 8 * d * w ∧
    kPanSixSlopeRestored = 139920417568 ∧
    kPanAccessCall - kPanSixSlopeRestored = 19972857140 ∧
    6 * kPanSixSlopeRestored < yukon ∧
    yukon - 6 * kPanSixSlopeRestored = 61197420066 ∧
    yukon < 7 * kPanSixSlopeRestored :=
  ⟨revert_le_tight d p q w H2, kPan_val.1, kPan_val.2.1, six_slope⟩

/-- Without H2 the original five-slope envelope remains, and six slopes fail. -/
theorem unconditional_five_slope_non_vacuous_and_tight :
    kPanAccessCall = 159893274708 ∧
    5 * kPanAccessCall < yukon ∧ yukon < 6 * kPanAccessCall ∧
    kPanDisjointTables = kPanAccessCall := by decide

theorem panToTarget_sections_clean_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s := by
  apply UnifiedDisjointTablesAndCoupledRevertTxCapMaster.panToTarget_sections_clean_non_vacuous_and_tight <;> assumption

theorem panToTarget_sections_length_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2).length := by
  apply UnifiedDisjointTablesAndCoupledRevertTxCapMaster.panToTarget_sections_length_non_vacuous_and_tight <;> assumption

theorem tx_dirty_cap_non_vacuous_and_tight (d_t w_t : Nat)
    (h : 21 * d_t + w_t ≤ M) :
    d_t ≤ 7989 ∧ 21 * 7989 ≤ M ∧ M < 21 * 7990 := by
  apply UnifiedDisjointTablesAndCoupledRevertTxCapMaster.tx_dirty_cap_non_vacuous_and_tight <;> assumption

theorem disjoint_partition_non_vacuous_and_tight (db dx D W : Nat)
    (hp : db + dx ≤ D) (hgas : 21 * D + W ≤ S) :
    21 * (db + dx) + W ≤ S ∧
    cycleTicks db dx ≤ 13 * (db + dx) ∧
    cycleTicks db dx ≤ 13 * D ∧
    cycleTicks 0 D = 13 * D ∧ cycleTicks D 0 = 2 * D ∧
    cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) := by
  apply UnifiedDisjointTablesAndCoupledRevertTxCapMaster.disjoint_partition_non_vacuous_and_tight <;> assumption

theorem forty_certified_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    portfolio.length = 40 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ k ∈ portfolio, k < 900719925474 ∧
      InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  exact UnifiedDisjointTablesAndCoupledRevertTxCapMaster.forty_certified_non_vacuous_and_tight cert

theorem submission_certificate_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) (K : Nat) (hk : K ∈ portfolio)
    (submission : InitE.Submission) (hs : submission = baselineWithFiniteK K) :
    K < 900719925474 ∧ InitE.Certificate submission (.finite K) := by
  apply UnifiedDisjointTablesAndCoupledRevertTxCapMaster.submission_certificate_non_vacuous_and_tight <;> assumption

theorem no_six_restore_non_vacuous_and_tight :
    feasible witness ∧ coupledCost witness = 155688931265 ∧
    yukon < 6 * coupledCost witness ∧
    ∃ l, feasible l ∧ yukon < 6 * coupledCost l := by
  exact UnifiedDisjointTablesAndCoupledRevertTxCapMaster.no_six_restore_non_vacuous_and_tight

/-- Alignment with the independently assembled self-contained forty-budget synthesis. -/
theorem self_contained_alignment_non_vacuous_and_tight :
    portfolio = SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio ∧
    portfolio.length = 40 ∧ portfolio.Pairwise (· < ·) ∧
    kPanDisjointTables = kPanStateRestoreCoupled ∧
    kPanDisjointTables = kPanAccessCall := by
  have hu := UnifiedDisjointTablesAndCoupledRevertTxCapMaster.unified_portfolios_non_vacuous_and_tight
  have hs := SelfContainedDisjointBlockTxAndFortyBudgetSynth.disjoint_master_and_self_contained_forty_portfolio_alignment_non_vacuous_and_tight 0
  exact ⟨hu.2.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2,
    hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩

/-- Coupled master: the conditional six-slope result coexists with the unconditional
five-slope bound, tx cap, disjoint partition, clean sections and forty submissions. -/
theorem integrated_master_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) (cert : CertificateAt 1212035192)
    (db dx D W d_t w_t : Nat) (hpart : db + dx ≤ D)
    (hpaid : 21 * D + W ≤ S) (htx : 21 * d_t + w_t ≤ M)
    (d p q w : Nat) (H2 : p + cycleUnits * q ≤ w) :
    (journalFlags [] [d_t, d_t] = [false, true] ∧
      dels [] [1, 1, 1, 2, 2] = 2 ∧ dels [1] [1, 1] = 0) ∧
    (100 + 100 = cycleUnits * 100 ∧ 19 * 100 + 100 = freshUnits * 100) ∧
    (8 * d * p + 13 * d * q ≤ 8 * d * w ∧
      kPanSixSlopeRestored = 139920417568 ∧
      kPanAccessCall - kPanSixSlopeRestored = 19972857140 ∧
      6 * kPanSixSlopeRestored < yukon ∧
      yukon - 6 * kPanSixSlopeRestored = 61197420066 ∧
      yukon < 7 * kPanSixSlopeRestored) ∧
    (kPanAccessCall = 159893274708 ∧
      5 * kPanAccessCall < yukon ∧ yukon < 6 * kPanAccessCall ∧
      kPanDisjointTables = kPanAccessCall) ∧
    (d_t ≤ 7989 ∧ 21 * 7989 ≤ M ∧ M < 21 * 7990) ∧
    (21 * (db + dx) + W ≤ S ∧
      cycleTicks db dx ≤ 13 * (db + dx) ∧ cycleTicks db dx ≤ 13 * D ∧
      cycleTicks 0 D = 13 * D ∧ cycleTicks D 0 = 2 * D ∧
      cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1)) ∧
    (feasible witness ∧ coupledCost witness = 155688931265 ∧
      yukon < 6 * coupledCost witness ∧
      ∃ l, feasible l ∧ yukon < 6 * coupledCost l) ∧
    (kPanCoupledRevertTxCap = 159893274708 ∧
      kPanCoupledRevertTxCap = kPanDisjointTables ∧
      kPanCoupledRevertTxCap = kPanStateRestoreCoupled ∧
      coupledCost witness ≤ kPanCoupledRevertTxCap ∧
      5 * kPanCoupledRevertTxCap < yukon ∧ yukon < 6 * kPanCoupledRevertTxCap) ∧
    (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    (portfolio.length = 40 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, K < 900719925474 ∧
        ∃ submission : InitE.Submission, submission = baselineWithFiniteK K ∧
          InitE.Certificate submission (.finite K)) := by
  exact ⟨⟨repeat_no_delete d_t, dels_distinct⟩, cycle_units,
    conditional_six_slope_non_vacuous_and_tight d p q w H2,
    unconditional_five_slope_non_vacuous_and_tight,
    UnifiedDisjointTablesAndCoupledRevertTxCapMaster.integrated_master_non_vacuous_and_tight
      arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h cert
      db dx D W d_t w_t hpart hpaid htx⟩

#print axioms repeat_no_delete_non_vacuous_and_tight
#print axioms dels_distinct_non_vacuous_and_tight
#print axioms cycle_units_non_vacuous_and_tight
#print axioms revert_le_tight_non_vacuous_and_tight
#print axioms conditional_six_slope_non_vacuous_and_tight
#print axioms unconditional_five_slope_non_vacuous_and_tight
#print axioms panToTarget_sections_clean_non_vacuous_and_tight
#print axioms panToTarget_sections_length_non_vacuous_and_tight
#print axioms tx_dirty_cap_non_vacuous_and_tight
#print axioms disjoint_partition_non_vacuous_and_tight
#print axioms forty_certified_non_vacuous_and_tight
#print axioms submission_certificate_non_vacuous_and_tight
#print axioms no_six_restore_non_vacuous_and_tight
#print axioms self_contained_alignment_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.DistinctDeleteCycleAndCoupledRevertMaster
