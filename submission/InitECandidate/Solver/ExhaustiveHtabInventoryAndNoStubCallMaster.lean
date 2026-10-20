import InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption
import InitECandidate.Solver.WordToWordNoStubCallAndFortyEightBudgetMaster
import InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_134: exhaustive inventory, exact absorption threshold, unconditional compiler
safety, and 48 finite budgets. No bound for all transient-storage tables is asserted.
Finite certificates retain the explicit base-certificate premise. -/
namespace InitECandidate.Solver.ExhaustiveHtabInventoryAndNoStubCallMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption (S tstoreTicks)
open _root_.InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption (kPanElevenTablesShared)
open _root_.InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (feasible witness coupledCost)
open _root_.InitECandidate.Solver.ElevenTablesSharedAbsorptionAndFortyEightBudgetMaster (portfolio)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth (fortyEightSharedClaims)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

theorem side_absorption_scalar_non_vacuous_and_tight (B U T blk : Nat) (hS : B + U ≤ S) (hblk : 40 * blk ≤ B * B)
    (hT : T ≤ 50000 * U) : blk + T ≤ 100000000000 :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.side_absorption_scalar B U T blk hS hblk hT

theorem general_side_regime_absorption_non_vacuous_and_tight (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum) :
    blk + (l.map Prod.fst).sum ≤ 100000000000 :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.general_side_regime_absorption l B blk hS hblk hslope

theorem slope_sum_non_vacuous_and_tight (l : List (Nat × Nat)) (h : ∀ p ∈ l, p.1 ≤ 50000 * p.2) :
    (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.slope_sum l h

theorem absorption_tight_non_vacuous_and_tight : 40 * 100000000000 = S * S ∧ 100000000000 + 0 = 100000000000 :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.absorption_tight

theorem threshold_sharp_non_vacuous_and_tight :
    ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B → T ≤ 50001 * U → blk + T ≤ 100000000000) :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.threshold_sharp

theorem known_slopes_non_vacuous_and_tight : 5 * 7989 ≤ 21 * 50000 ∧ 5 * 5611 ≤ 30 * 50000 ∧
    167772 + 2280 ≤ 60 * 50000 ∧ 2 * 6250 ≤ 320 * 50000 :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.known_slopes

theorem tstore_slope_exceeds_non_vacuous_and_tight : tstoreTicks 83826 - tstoreTicks 83825 = 2 * 83825 ∧ 50000 < 83825 :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.tstore_slope_exceeds

theorem tstore_tx_budget_non_vacuous_and_tight : 120 + 2 * 83826 ≤ 167772 ∧ 11 * 167772 + 120 + 2 * 77194 ≤ S :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.tstore_tx_budget

theorem tstore_witness_non_vacuous_and_tight : 11 * tstoreTicks 83826 + tstoreTicks 77194 = 83252695392 :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.tstore_witness

theorem tstore_sensitivity_non_vacuous_and_tight :
    83252695392 ≤ 50000 * (11 * 2 * 83826 + 2 * 77194) ∧
      2 * tstoreTicks 167652 = 56214050904 ∧ 50000 * 167772 < 2 * tstoreTicks 167652 :=
  GuestExhaustiveHtabInventoryAndSlopeAbsorption.tstore_sensitivity

theorem panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat)
    (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum) :
    (
    ∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true)) ∧
    blk + (l.map Prod.fst).sum ≤ 100000000000 ∧
    (¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B →
      T ≤ 50001 * U → blk + T ≤ 100000000000)) ∧
    kPanElevenTablesShared = 156088992805 ∧
    (feasible witness ∧ coupledCost witness = 155688931265 ∧
      coupledCost witness ≤ kPanElevenTablesShared ∧
      kPanElevenTablesShared - coupledCost witness = 400061540 ∧
      400061540 * 10000 < 26 * 156088992805 ∧
      400061540 * 10000 < 26 * 155688931265) := by
  exact ⟨WordToWordNoStubCallAndFortyEightBudgetMaster.panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
      arch prog wc ac perf info j bd ptr f,
    general_side_regime_absorption_non_vacuous_and_tight l B blk hS hblk hslope,
    threshold_sharp_non_vacuous_and_tight, by decide,
    WordToWordNoStubCallAndFortyEightBudgetMaster.bracket_non_vacuous_and_tight⟩

/-- All 48 budgets are strictly ordered below Yukon; semantic certificates are
lifted from the base certificate. The self-contained synth also validates the
48 concrete finite claim payloads. -/
theorem forty_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (portfolio.length = 48 ∧ portfolio.Pairwise (· < ·) ∧
      ∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    fortyEightSharedClaims.length = 48 ∧
    fortyEightSharedClaims.map Prod.fst = portfolio ∧
    (∀ entry ∈ fortyEightSharedClaims,
      entry.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim entry.1 entry.2 = true) := by
  have hc := WordToWordNoStubCallAndFortyEightBudgetMaster.forty_eight_certified_non_vacuous_and_tight cert
  have hj := SelfContainedPanToWordNoStubCallAndFortyEightBudgetSynth.forty_eight_shared_claims_valid_and_within_128_bytes_non_vacuous_and_tight 1
  exact ⟨WordToWordNoStubCallAndFortyEightBudgetMaster.portfolio_shape_non_vacuous_and_tight,
    fun K hK => (hc.2.2 K hK).2, hj.1, hj.2.1, hj.2.2.1⟩

#print axioms side_absorption_scalar_non_vacuous_and_tight
#print axioms general_side_regime_absorption_non_vacuous_and_tight
#print axioms slope_sum_non_vacuous_and_tight
#print axioms absorption_tight_non_vacuous_and_tight
#print axioms threshold_sharp_non_vacuous_and_tight
#print axioms known_slopes_non_vacuous_and_tight
#print axioms tstore_slope_exceeds_non_vacuous_and_tight
#print axioms tstore_tx_budget_non_vacuous_and_tight
#print axioms tstore_witness_non_vacuous_and_tight
#print axioms tstore_sensitivity_non_vacuous_and_tight
#print axioms panToStackNames_NoSt_and_NoStubCall_unconditional_non_vacuous_and_tight
#print axioms forty_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.ExhaustiveHtabInventoryAndNoStubCallMaster
