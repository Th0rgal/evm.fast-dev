import InitECandidate.Solver.StateRestoreCoupledAndFortyBudgetMaster
import InitECandidate.Solver.SelfContainedFortyBudgetPortfolioSynth
import InitECandidate.Solver.SelfContainedAccessListCallStackAndLabToTargetSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Coupled state restoration, section preservation and the forty-budget portfolio.
The deletion-count tightening is refuted. Finite execution certificates retain
an explicit base CertificateAt premise; structural preservation alone does not
establish an execution clock for a modified ROM. -/
namespace InitECandidate.Solver.FortyBudgetPortfolioAndStateRestoreMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabFilter
open InitECandidate.Solver
open GuestAccessListAndCallStackDominance GuestSubBlockTxSplittingDominance
open _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope (kPanUnifiedAllTables)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S)
open PanToLabSectionAndStackRemoveClock
open LabToTargetSectionCleanPreservation
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt certificate_lift_non_vacuous_and_tight)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

open _root_.InitECandidate.Solver.AccessListCallStackAndLabToTargetMaster (accessCallSlope3UnrolledK accessCallSlope3K accessCallSlope5UnrolledK accessCallSlope5K accessCallTargets)
open GuestStateRestoreCoupledTightening

abbrev portfolio := StateRestoreCoupledAndFortyBudgetMaster.portfolio

variable {width : Nat} [NeZero width]

theorem restore_restore_dispatch_non_vacuous_and_tight (p : Bool) : restoreOf p = .del ↔ p = false := by
  exact StateRestoreCoupledAndFortyBudgetMaster.restore_restore_dispatch_non_vacuous_and_tight p

theorem restore_noop_warm_gas_non_vacuous_and_tight (oc : Bool) : sstoreGas true oc true = 100 := by
  exact StateRestoreCoupledAndFortyBudgetMaster.restore_noop_warm_gas_non_vacuous_and_tight oc

theorem restore_dels_per_call_non_vacuous_and_tight (k : Nat) : delsPerCall k = k := by
  exact StateRestoreCoupledAndFortyBudgetMaster.restore_dels_per_call_non_vacuous_and_tight k

theorem restore_del_bound_refuted_non_vacuous_and_tight : ¬ (1000 * delsPerCall 100 ≤ 0 + 0) := by
  exact StateRestoreCoupledAndFortyBudgetMaster.restore_del_bound_refuted_non_vacuous_and_tight

theorem restore_hypothetical_fix_non_vacuous_and_tight :
    6 * (136116135658 + 3804281910) < yukon ∧ ¬ (6 * kPanStateRestoreCoupled < yukon) := by
  exact StateRestoreCoupledAndFortyBudgetMaster.restore_hypothetical_fix_non_vacuous_and_tight

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
  apply StateRestoreCoupledAndFortyBudgetMaster.panToTarget_sections_clean_non_vacuous_and_tight <;> assumption

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
  apply StateRestoreCoupledAndFortyBudgetMaster.panToTarget_sections_length_non_vacuous_and_tight <;> assumption

theorem lab_split_prefix_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat))
    (p : List (Nat × Nat)) (P : Nat)
    (h : 21*sD l + 20*sR l + 26*sA l + 21*sC l + sW l ≤ S) :
    (l.map localCost).sum + 41935*sR l ≤ 95238095238 ∧
    prefixCost p P ≤ (P + (p.map Prod.fst).sum) * (p.map Prod.snd).sum := by
  exact StateRestoreCoupledAndFortyBudgetMaster.lab_split_prefix_non_vacuous_and_tight l p P h

theorem forty_certified_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    portfolio.length = 40 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ k ∈ portfolio, k < 900719925474 ∧
      InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  exact StateRestoreCoupledAndFortyBudgetMaster.forty_certified_non_vacuous_and_tight cert

/-- The two independently assembled ordered portfolios coincide entry for entry. -/
theorem portfolio_unification_non_vacuous_and_tight :
    portfolio = SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio := by decide

/-- Exact increments from the nine-table envelope to the restored call/access envelope. -/
theorem exact_slope_gaps_non_vacuous_and_tight :
    kPanUnifiedAllTables = 136116135658 ∧
    kPanStateRestoreCoupled = 159893274708 ∧
    kPanStateRestoreCoupled - kPanUnifiedAllTables = 23777139050 ∧
    (9332 + 3 * kPanStateRestoreCoupled) - (9332 + 3 * kPanUnifiedAllTables) = 71331417150 ∧
    (23132 + 3 * kPanStateRestoreCoupled) - (23132 + 3 * kPanUnifiedAllTables) = 71331417150 ∧
    (9332 + 5 * kPanStateRestoreCoupled) - (9332 + 5 * kPanUnifiedAllTables) = 118885695250 ∧
    (23132 + 5 * kPanStateRestoreCoupled) - (23132 + 5 * kPanUnifiedAllTables) = 118885695250 ∧
    5 * kPanStateRestoreCoupled < 900719925474 ∧
    900719925474 < 6 * kPanStateRestoreCoupled := by decide

/-- Certificate lifting retains the explicit base semantic certificate. -/
theorem both_portfolios_certified_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    portfolio.length = 40 ∧ portfolio.Pairwise (· < ·) ∧
    SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio = portfolio ∧
    ∀ K ∈ SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio,
      K < 900719925474 ∧ InitE.Certificate (baselineWithFiniteK K) (.finite K) := by
  have h := forty_certified_non_vacuous_and_tight cert
  exact ⟨h.1, h.2.1, portfolio_unification_non_vacuous_and_tight.symm,
    by simpa only [← portfolio_unification_non_vacuous_and_tight] using h.2.2⟩

theorem access_list_and_call_stack_dominance_and_slope_threshold_non_vacuous_and_tight
    (Kal Aal D A C R W d c n k : Nat) (l : List (Nat × Nat))
    (hal : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2000000)
    (hrev : (l.map (fun p => p.1 * p.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238)
    (hdepth : ¬ (d + 1 > 1024)) :
    (alAddrGas = 4180 ∧ alKeyGas = 4048) ∧
    (26 * 100 < alAddrGas ∧ 21 * 100 < alKeyGas ∧ 20 * 100 < alKeyGas) ∧
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2000000 ∧
    undoTicks d = 5 * d ∧
    revertCost l = 5 * (l.map (fun p => p.1 * p.2)).sum ∧
    revertCost l ≤ 19972857140 ∧
    (5 * c * n ≤ 3804281910 ∧ 21 * 7989 ≤ 167772 ∧ 167772 < 21 * 7990) ∧
    d ≤ 1023 ∧
    kPanAccessCall = 159893274708 ∧
    (3 * kPanAccessCall < yukon ∧ 4 * kPanAccessCall < yukon ∧ 5 * kPanAccessCall < yukon ∧
      yukon < 6 * kPanAccessCall) ∧
    ((k * kPanAccessCall < yukon ↔ k ≤ 5) ∧ yukon - 5 * kPanAccessCall = 101253551934) := by
  apply SelfContainedAccessListCallStackAndLabToTargetSynth.access_list_and_call_stack_dominance_and_slope_threshold_non_vacuous_and_tight <;> assumption

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
    (probes : List (Nat × Nat)) (c n base : Nat)
    (hp : (probes.map (fun p => p.1 * p.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238) (hb : base ≤ kPanUnifiedAllTables)
    (l : List (Nat × Nat × Nat × Nat × Nat)) (Kal Aal : Nat)
    (hgas : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2000000) :
    ((9332 + 3 * kPanStateRestoreCoupled) - (9332 + 3 * kPanUnifiedAllTables) = 71331417150 ∧
     (9332 + 5 * kPanStateRestoreCoupled) - (9332 + 5 * kPanUnifiedAllTables) = 118885695250) ∧
    (6 * (136116135658 + 3804281910) < yukon ∧ ¬ (6 * kPanStateRestoreCoupled < yukon)) ∧
    portfolio = SelfContainedFortyBudgetPortfolioSynth.fortyAccessCallPortfolio ∧
    ((ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s) ∧
    L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2).length ∧
    base + revertCost probes + 5 * c * n ≤ kPanAccessCall ∧
    42 * (l.map localCost).sum ≤ S * S ∧
    (∀ k ∈ portfolio, k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k))) ∧
    (∀ p : Bool, restoreOf p = .del ↔ p = false) ∧
    (∀ oc : Bool, sstoreGas true oc true = 100) ∧
    (∀ k : Nat, delsPerCall k = k) ∧
    (¬ (1000 * delsPerCall 100 ≤ 0 + 0)) ∧
    kPanStateRestoreCoupled = 159893274708 ∧
    5 * kPanStateRestoreCoupled < yukon ∧
    yukon - 5 * kPanStateRestoreCoupled = 101253551934 := by
  refine ⟨by decide, restore_hypothetical_fix_non_vacuous_and_tight,
    portfolio_unification_non_vacuous_and_tight, ?_⟩
  apply StateRestoreCoupledAndFortyBudgetMaster.integrated_master_non_vacuous_and_tight <;> assumption

#print axioms restore_restore_dispatch_non_vacuous_and_tight
#print axioms restore_noop_warm_gas_non_vacuous_and_tight
#print axioms restore_dels_per_call_non_vacuous_and_tight
#print axioms restore_del_bound_refuted_non_vacuous_and_tight
#print axioms restore_hypothetical_fix_non_vacuous_and_tight
#print axioms panToTarget_sections_clean_non_vacuous_and_tight
#print axioms panToTarget_sections_length_non_vacuous_and_tight
#print axioms lab_split_prefix_non_vacuous_and_tight
#print axioms forty_certified_non_vacuous_and_tight
#print axioms portfolio_unification_non_vacuous_and_tight
#print axioms exact_slope_gaps_non_vacuous_and_tight
#print axioms both_portfolios_certified_non_vacuous_and_tight
#print axioms access_list_and_call_stack_dominance_and_slope_threshold_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.FortyBudgetPortfolioAndStateRestoreMaster
