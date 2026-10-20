import InitECandidate.Solver.GuestAccessListAndCallStackDominance
import InitECandidate.Solver.LabToTargetAndSubBlockThirtySixBudgetMaster
import InitECandidate.Solver.SelfContainedLabToTargetAndSubBlockSynth

set_option autoImplicit false
set_option maxRecDepth 200000

namespace InitECandidate.Solver.AccessListCallStackThirtySixBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open _root_.InitECandidate.Solver.GuestMergeTxUnionEnvelope (locCoup mergeLin)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope (F G kPanUnifiedAllTables)
open SelfContainedBoundedCertificate UnrolledTwelveCandidatePortfolio
open GuestSubBlockTxSplittingDominance
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open PanToStackToLabUnconditionalNoStoreConsts
open PanToLabSectionAndStackRemoveClock
open _root_.InitECandidate.Solver.LabToTargetSectionCleanPreservation (Sec ids)

open GuestAccessListAndCallStackDominance

/-! Arithmetic envelopes and structural preservation do not imply a target execution
certificate. All finite certificates below retain the explicit baseline premise. -/

def accessSlope3UnrolledK : Nat := 9332 + 3 * kPanAccessCall
def accessSlope3K : Nat := 23132 + 3 * kPanAccessCall
def accessSlope5UnrolledK : Nat := 9332 + 5 * kPanAccessCall
def accessSlope5K : Nat := 23132 + 5 * kPanAccessCall

def addedBudgets : List Nat :=
  [accessSlope3UnrolledK, accessSlope3K, accessSlope5UnrolledK, accessSlope5K]

def portfolio : List Nat :=
  (LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio ++ addedBudgets).insertionSort (· ≤ ·)

theorem al_costs_non_vacuous_and_tight : alAddrGas = 4180 ∧ alKeyGas = 4048 := by
  apply GuestAccessListAndCallStackDominance.al_costs <;> assumption

theorem al_dominated_non_vacuous_and_tight : 26 * 100 < alAddrGas ∧ 21 * 100 < alKeyGas ∧ 20 * 100 < alKeyGas := by
  apply GuestAccessListAndCallStackDominance.al_dominated <;> assumption

theorem al_budget_non_vacuous_and_tight (Kal Aal D A C R W : Nat)
    (h : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2000000) :
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2000000 := by
  apply GuestAccessListAndCallStackDominance.al_budget <;> assumption

theorem undo_eq_non_vacuous_and_tight (d : Nat) : undoTicks d = 5 * d := by
  apply GuestAccessListAndCallStackDominance.undo_eq <;> assumption

theorem revert_eq_non_vacuous_and_tight (l : List (Nat × Nat)) :
    revertCost l = 5 * (l.map (fun p => p.1 * p.2)).sum := by
  apply GuestAccessListAndCallStackDominance.revert_eq <;> assumption

theorem revert_le_non_vacuous_and_tight (l : List (Nat × Nat)) (h : (l.map (fun p => p.1 * p.2)).sum ≤ 3994571428) :
    revertCost l ≤ 19972857140 := by
  apply GuestAccessListAndCallStackDominance.revert_le <;> assumption

theorem truncate_le_non_vacuous_and_tight (c n : Nat) (hc : c ≤ 7989) (hn : n ≤ 95238) :
    5 * c * n ≤ 3804281910 ∧ 21 * 7989 ≤ 167772 ∧ 167772 < 21 * 7990 := by
  apply GuestAccessListAndCallStackDominance.truncate_le <;> assumption

theorem depth_guard_non_vacuous_and_tight (d : Nat) (h : ¬ (d + 1 > 1024)) : d ≤ 1023 := by
  apply GuestAccessListAndCallStackDominance.depth_guard <;> assumption

theorem kPanAccessCall_val_non_vacuous_and_tight : kPanAccessCall = 159893274708 := by
  apply GuestAccessListAndCallStackDominance.kPanAccessCall_val <;> assumption

theorem slopes_non_vacuous_and_tight :
    3 * kPanAccessCall < yukon ∧ 4 * kPanAccessCall < yukon ∧ 5 * kPanAccessCall < yukon ∧
      yukon < 6 * kPanAccessCall := by
  apply GuestAccessListAndCallStackDominance.slopes <;> assumption

theorem threshold_non_vacuous_and_tight (k : Nat) :
    (k * kPanAccessCall < yukon ↔ k ≤ 5) ∧ yukon - 5 * kPanAccessCall = 101253551934 := by
  apply GuestAccessListAndCallStackDominance.threshold <;> assumption

variable {width : Nat} [NeZero width]

theorem split_local_le_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat)) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.split_local_le_non_vacuous_and_tight <;> assumption

theorem split_strict_non_vacuous_and_tight :
    localCost (1, 1, 1, 1, 1) + localCost (1, 1, 1, 1, 1) = 40 ∧ localCost (2, 2, 2, 2, 2) = 80 := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.split_strict_non_vacuous_and_tight <;> assumption

theorem prefix_le_non_vacuous_and_tight (l : List (Nat × Nat)) (P : Nat) :
    prefixCost l P ≤ (P + (l.map Prod.fst).sum) * (l.map Prod.snd).sum := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.prefix_le_non_vacuous_and_tight <;> assumption

theorem prefix_tight_non_vacuous_and_tight (D W : Nat) : prefixCost [(D, W)] 0 = D * W := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.prefix_tight_non_vacuous_and_tight <;> assumption

theorem prefix_strict_non_vacuous_and_tight : prefixCost [(1, 1), (1, 1)] 0 = 3 ∧ 3 < (0 + 2) * 2 := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.prefix_strict_non_vacuous_and_tight <;> assumption

theorem reset_bound_non_vacuous_and_tight : 8 * (6 + 1 + (1 + 64 / 32 + 3)) + 2 ≤ txResetTicks := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.reset_bound_non_vacuous_and_tight <;> assumption

theorem reset_absorbed_non_vacuous_and_tight (T : Nat) (h : txMinUnits * T ≤ 2000000) :
    txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666 := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.reset_absorbed_non_vacuous_and_tight <;> assumption

theorem max_tx_reset_non_vacuous_and_tight : txMinUnits * 16666 ≤ 2000000 ∧ 2000000 < txMinUnits * 16667 ∧
    txResetTicks * 16666 = 3333200 := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.max_tx_reset_non_vacuous_and_tight <;> assumption

theorem subblock_master_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat)) (bound : Nat)
    (hb : localCost (sD l, sR l, sA l, sC l, sW l) ≤ bound) :
    (l.map localCost).sum ≤ bound ∧ 6 * kPanUnifiedAllTables < yukon ∧
      kPanUnifiedAllTables = 136116135658 := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.subblock_master_non_vacuous_and_tight <;> assumption

theorem ids_removeLabels_non_vacuous_and_tight (ic : Nat) (config : AsmConfigExact width) (pos : Nat)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (L L' : List (Sec width))
    (labs' : Spt (Spt Nat)) (h : removeLabels ic config pos labs ffis L = some (L', labs')) :
    ids L' = ids L := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.ids_removeLabels_non_vacuous_and_tight <;> assumption

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
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.panToTarget_sections_clean_non_vacuous_and_tight <;> assumption

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
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.panToTarget_sections_length_non_vacuous_and_tight <;> assumption

theorem split_coupled_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat))
    (h : 21*sD l + 20*sR l + 26*sA l + 21*sC l + sW l ≤ S) :
    (l.map localCost).sum + 41935*sR l ≤ 95238095238 := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.split_coupled_non_vacuous_and_tight <;> assumption

theorem split_prefix_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat))
    (p : List (Nat × Nat)) (P : Nat)
    (h : 21*sD l + 20*sR l + 26*sA l + 21*sC l + sW l ≤ S) :
    (l.map localCost).sum + 41935*sR l ≤ 95238095238 ∧
    prefixCost p P ≤ (P + (p.map Prod.fst).sum) * (p.map Prod.snd).sum := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.split_prefix_non_vacuous_and_tight <;> assumption

theorem values_non_vacuous_and_tight :
    accessSlope3UnrolledK = 479679833456 ∧ accessSlope3K = 479679847256 ∧
    accessSlope5UnrolledK = 799466382872 ∧ accessSlope5K = 799466396672 := by decide

theorem added_bounds_non_vacuous_and_tight :
    addedBudgets.length = 4 ∧ addedBudgets.Pairwise (· < ·) ∧
    ∀ k ∈ addedBudgets, 1212035192 ≤ k ∧ k < yukon := by decide

theorem portfolio_non_vacuous_and_tight :
    portfolio.length = 40 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon := by decide

theorem old_coverage_non_vacuous_and_tight :
    ∀ k ∈ LabToTargetAndSubBlockThirtySixBudgetMaster.portfolio, k ∈ portfolio := by decide

theorem new_coverage_non_vacuous_and_tight :
    ∀ k ∈ addedBudgets, k ∈ portfolio := by decide

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  intro k hk
  exact certificate_lift_non_vacuous_and_tight 1212035192 k
    (portfolio_non_vacuous_and_tight.2.2 k hk).1 hc

theorem target_tiers_non_vacuous_and_tight (cost : Nat) (h : cost ≤ kPanAccessCall) :
    9332 + 3*cost ≤ accessSlope3UnrolledK ∧ 23132 + 3*cost ≤ accessSlope3K ∧
    9332 + 5*cost ≤ accessSlope5UnrolledK ∧ 23132 + 5*cost ≤ accessSlope5K ∧
    accessSlope5K < yukon := by
  have hv := values_non_vacuous_and_tight
  have hk := kPanAccessCall_val
  have hy : yukon = 900719925474 := by decide
  omega

theorem split_revert_master_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat)) (r : List (Nat × Nat))
    (T Tloc Tlin c n : Nat)
    (budget : 21*sD l + 20*sR l + 26*sA l + 21*sC l + sW l ≤ S)
    (ht : txMinUnits*T ≤ 2000000) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hr : (r.map (fun p => p.1*p.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238) :
    let cost := linear + Tloc + ((l.map localCost).sum + 41935*sR l) + Tlin +
      revertCost r + 5*c*n
    cost ≤ kPanAccessCall ∧
    (9332+3*cost ≤ accessSlope3UnrolledK ∧ 23132+3*cost ≤ accessSlope3K ∧
     9332+5*cost ≤ accessSlope5UnrolledK ∧ 23132+5*cost ≤ accessSlope5K ∧
     accessSlope5K < yukon) ∧
    txResetTicks*T ≤ 18*(12000*T) ∧ T ≤ 16666 ∧
    portfolio.length = 40 ∧ ∀ k ∈ portfolio, k < yukon := by
  have hs := LabToTargetAndSubBlockThirtySixBudgetMaster.split_four_tiers_non_vacuous_and_tight
    l T Tloc Tlin budget ht hloc hlin
  have hrb := revert_le r hr
  have htb := (truncate_le c n hc hn).1
  have hb : linear + Tloc + ((l.map localCost).sum + 41935*sR l) + Tlin +
      revertCost r + 5*c*n ≤ kPanAccessCall := by
    unfold kPanAccessCall
    omega
  exact ⟨hb, target_tiers_non_vacuous_and_tight _ hb, hs.2.2.2.2.2.1,
    hs.2.2.2.2.2.2.1, portfolio_non_vacuous_and_tight.1,
    fun k hk => (portfolio_non_vacuous_and_tight.2.2 k hk).2⟩

/-- Combined structural preservation, call/revert envelope and conditional finite
certificates for the full forty-budget portfolio. removeLabels success and
baseline certification are explicit hypotheses. -/
theorem integrated_master_non_vacuous_and_tight
    (l : List (Nat × Nat × Nat × Nat × Nat)) (r : List (Nat × Nat))
    (T Tloc Tlin c n : Nat)
    (budget : 21*sD l + 20*sR l + 26*sA l + 21*sC l + sW l ≤ S)
    (ht : txMinUnits*T ≤ 2000000) (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin)
    (hr : (r.map (fun p => p.1*p.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238) (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (base : CertificateAt 1212035192) :
    (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    (L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2).length) ∧
    (let cost := linear + Tloc + ((l.map localCost).sum + 41935*sR l) + Tlin +
      revertCost r + 5*c*n
    cost ≤ kPanAccessCall ∧
    (9332+3*cost ≤ accessSlope3UnrolledK ∧ 23132+3*cost ≤ accessSlope3K ∧
     9332+5*cost ≤ accessSlope5UnrolledK ∧ 23132+5*cost ≤ accessSlope5K ∧
     accessSlope5K < yukon) ∧
    txResetTicks*T ≤ 18*(12000*T) ∧ T ≤ 16666 ∧
    portfolio.length = 40 ∧ ∀ k ∈ portfolio, k < yukon) ∧
    (∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k)) := by
  exact ⟨panToTarget_sections_clean_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off
      ic pos labs ffis L' labs' h,
    panToTarget_sections_length_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off
      ic pos labs ffis L' labs' h,
    split_revert_master_non_vacuous_and_tight l r T Tloc Tlin c n budget ht hloc hlin hr hc hn,
    portfolio_certificates_non_vacuous_and_tight base⟩

/-- Paid access-list entries can be absorbed before applying the coupled envelope. -/
theorem access_coupled_non_vacuous_and_tight (Kal Aal D A C R W : Nat)
    (h : 40*Kal + 41*Aal + 21*D + 20*R + 26*A + 21*C + W ≤ 2000000) :
    F (D+Kal) R (A+Aal) C W ≤ 95238095238 := by
  exact LabToTargetAndSubBlockThirtySixBudgetMaster.unified_five_var_coupled_envelope_non_vacuous_and_tight
    (D+Kal) R (A+Aal) C W (al_budget Kal Aal D A C R W h)

#print axioms al_costs_non_vacuous_and_tight
#print axioms al_dominated_non_vacuous_and_tight
#print axioms al_budget_non_vacuous_and_tight
#print axioms undo_eq_non_vacuous_and_tight
#print axioms revert_eq_non_vacuous_and_tight
#print axioms revert_le_non_vacuous_and_tight
#print axioms truncate_le_non_vacuous_and_tight
#print axioms depth_guard_non_vacuous_and_tight
#print axioms kPanAccessCall_val_non_vacuous_and_tight
#print axioms slopes_non_vacuous_and_tight
#print axioms threshold_non_vacuous_and_tight
#print axioms split_local_le_non_vacuous_and_tight
#print axioms split_strict_non_vacuous_and_tight
#print axioms prefix_le_non_vacuous_and_tight
#print axioms prefix_tight_non_vacuous_and_tight
#print axioms prefix_strict_non_vacuous_and_tight
#print axioms reset_bound_non_vacuous_and_tight
#print axioms reset_absorbed_non_vacuous_and_tight
#print axioms max_tx_reset_non_vacuous_and_tight
#print axioms subblock_master_non_vacuous_and_tight
#print axioms ids_removeLabels_non_vacuous_and_tight
#print axioms panToTarget_sections_clean_non_vacuous_and_tight
#print axioms panToTarget_sections_length_non_vacuous_and_tight
#print axioms split_coupled_non_vacuous_and_tight
#print axioms split_prefix_non_vacuous_and_tight
#print axioms values_non_vacuous_and_tight
#print axioms added_bounds_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms old_coverage_non_vacuous_and_tight
#print axioms new_coverage_non_vacuous_and_tight
#print axioms portfolio_certificates_non_vacuous_and_tight
#print axioms target_tiers_non_vacuous_and_tight
#print axioms split_revert_master_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight
#print axioms access_coupled_non_vacuous_and_tight

end InitECandidate.Solver.AccessListCallStackThirtySixBudgetMaster
