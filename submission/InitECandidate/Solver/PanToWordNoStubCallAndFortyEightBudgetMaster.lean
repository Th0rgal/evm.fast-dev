import InitECandidate.Solver.PanToWordNoStubCall
import InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster
import InitECandidate.Solver.SelfContainedWarmAccessSetAndFortyFourBudgetSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_129. Unconditional frontend call safety, shared eleven-table absorption,
strict forty-eight-budget portfolio and conditional semantic certificates.
Finite clock certificates require the semantic base certificate; call safety does not. -/
namespace InitECandidate.Solver.PanToWordNoStubCallAndFortyEightBudgetMaster

open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Solver
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (WordNoStubCall)
open _root_.InitECandidate.Solver.PanToWordNoStubCall (TgtGood)
open _root_.InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (M S kPanElevenTablesShared)
open _root_.InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (feasible witness coupledCost)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster (portfolio)
open _root_.InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound (enter warmN truncDels)

theorem panToWord_NoStubCall_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : Compiler.Encoders.Asm.AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width)) :
    ∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true :=
  PanToWordNoStubCall.panToWord_NoStubCall arch prog

theorem panToWord_names_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : Compiler.Encoders.Asm.AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width)) :
    ∀ y ∈ panToWordCompileProgHOL arch prog, 64 ≤ y.1 :=
  PanToWordNoStubCall.panToWord_names arch prog

theorem tgtGood_rejects_stub_non_vacuous_and_tight : ¬ TgtGood (some storeConstsStubLocation) :=
  PanToWordNoStubCall.tgtGood_rejects_stub

theorem tgtGood_accepts_non_vacuous_and_tight : TgtGood (some 0) ∧ TgtGood (some 64) ∧ ¬ TgtGood none :=
  PanToWordNoStubCall.tgtGood_accepts

theorem wordNoStubCall_tight_non_vacuous_and_tight {α : Type} :
    WordNoStubCall (WordLangProgHOL.call (α := α) none (some storeConstsStubLocation) [] none) = false ∧
    WordNoStubCall (WordLangProgHOL.call (α := α) none (some 64) [] none) = true :=
  PanToWordNoStubCall.wordNoStubCall_tight (α := α)

theorem shared_absorption_non_vacuous_and_tight (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    blk + 13 * loc + t2 + t3 + t4 ≤ 151929428571 :=
  ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.shared_absorption_non_vacuous_and_tight B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4

theorem bracket_non_vacuous_and_tight :
    feasible witness ∧ coupledCost witness = 155688931265 ∧
    coupledCost witness ≤ kPanElevenTablesShared ∧
    kPanElevenTablesShared - coupledCost witness = 400061540 ∧
    400061540 * 10000 < 26 * 156088992805 ∧
    400061540 * 10000 < 26 * 155688931265 :=
  ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.bracket_non_vacuous_and_tight

theorem five_margin_non_vacuous_and_tight :
    5 * kPanElevenTablesShared < yukon ∧
    yukon - 5 * kPanElevenTablesShared = 120274961449 :=
  ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.five_margin_non_vacuous_and_tight

theorem portfolio_shape_non_vacuous_and_tight :
    portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474 :=
  ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.portfolio_shape_non_vacuous_and_tight

theorem forty_eight_certified_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ K ∈ portfolio, K < 900719925474 ∧
      InitE.Certificate (baselineWithFiniteK K) (.finite K) :=
  ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.forty_eight_certified_non_vacuous_and_tight cert

/-- Both frontend properties hold for every source, without a source invariant. -/
theorem frontend_safe_names_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) :
    ∀ y ∈ panToWordCompileProgHOL arch prog,
      WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1 := by
  intro y hy
  exact ⟨panToWord_NoStubCall_non_vacuous_and_tight arch prog y hy,
    panToWord_names_non_vacuous_and_tight arch prog y hy⟩

/-- Joint master: unconditional frontend safety and arithmetic envelope;
semantic certification of the 48 tiers is explicitly conditional. Warm rollback
is re-exported from the third self-contained parent for arbitrary frame sizes. -/
theorem integrated_master_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : Compiler.Encoders.Asm.AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width))
    (cert : CertificateAt 1212035192) (n k : Nat)
    (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hb : 40 * blk ≤ B * B) (hl : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3)
    (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    (∀ y ∈ panToWordCompileProgHOL arch prog,
      WordNoStubCall y.2.2 = true ∧ 64 ≤ y.1) ∧
    blk + 13 * loc + t2 + t3 + t4 ≤ 151929428571 ∧
    kPanElevenTablesShared = 156088992805 ∧
    (feasible witness ∧ coupledCost witness = 155688931265 ∧
     coupledCost witness ≤ kPanElevenTablesShared ∧
     kPanElevenTablesShared - coupledCost witness = 400061540 ∧
     400061540 * 10000 < 26 * 156088992805 ∧
     400061540 * 10000 < 26 * 155688931265) ∧
    (5 * kPanElevenTablesShared < yukon ∧
     yukon - 5 * kPanElevenTablesShared = 120274961449) ∧
    (yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness) ∧
    (truncDels (warmN (enter n) k) = k ∧
     (warmN (enter n) k).size - truncDels (warmN (enter n) k) = n) ∧
    (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
     ∀ K ∈ portfolio, K < 900719925474 ∧
       InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  have hw := SelfContainedWarmAccessSetAndFortyFourBudgetSynth.guest_warm_access_set_and_rollback_bound_complete_audit_non_vacuous_and_tight
    n k 0 0 0 0 (by decide) (by decide) (by decide) (by decide)
  exact ⟨frontend_safe_names_non_vacuous_and_tight arch prog,
    shared_absorption_non_vacuous_and_tight B u2 u3 u4 blk loc t2 t3 t4 hS hb hl h2 h3 h4,
    ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.kPan_val_non_vacuous_and_tight.1,
    bracket_non_vacuous_and_tight, five_margin_non_vacuous_and_tight,
    ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster.six_fails_non_vacuous_and_tight,
    ⟨hw.1, hw.2.1⟩, forty_eight_certified_non_vacuous_and_tight cert⟩

#print axioms panToWord_NoStubCall_non_vacuous_and_tight
#print axioms panToWord_names_non_vacuous_and_tight
#print axioms tgtGood_rejects_stub_non_vacuous_and_tight
#print axioms tgtGood_accepts_non_vacuous_and_tight
#print axioms wordNoStubCall_tight_non_vacuous_and_tight
#print axioms shared_absorption_non_vacuous_and_tight
#print axioms bracket_non_vacuous_and_tight
#print axioms five_margin_non_vacuous_and_tight
#print axioms portfolio_shape_non_vacuous_and_tight
#print axioms forty_eight_certified_non_vacuous_and_tight
#print axioms frontend_safe_names_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.PanToWordNoStubCallAndFortyEightBudgetMaster
