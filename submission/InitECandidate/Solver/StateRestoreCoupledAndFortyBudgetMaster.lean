import InitECandidate.Solver.GuestStateRestoreCoupledTightening
import InitECandidate.Solver.AccessListCallStackAndLabToTargetMaster
import InitECandidate.Solver.LabToTargetAndSubBlockThirtySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Coupled state restoration, section preservation and the forty-budget portfolio.
The deletion-count tightening is refuted. Finite execution certificates retain
an explicit base CertificateAt premise; structural preservation alone does not
establish an execution clock for a modified ROM. -/
namespace InitECandidate.Solver.StateRestoreCoupledAndFortyBudgetMaster

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

abbrev portfolio := AccessListCallStackAndLabToTargetMaster.portfolio

variable {width : Nat} [NeZero width]

theorem restore_restore_dispatch_non_vacuous_and_tight (p : Bool) : restoreOf p = .del ↔ p = false := by
  apply GuestStateRestoreCoupledTightening.restore_dispatch <;> assumption

theorem restore_noop_warm_gas_non_vacuous_and_tight (oc : Bool) : sstoreGas true oc true = 100 := by
  apply GuestStateRestoreCoupledTightening.noop_warm_gas <;> assumption

theorem restore_changing_write_gas_non_vacuous_and_tight : sstoreGas true true false = 10100 ∧ sstoreGas false true false = 12100 := by
  apply GuestStateRestoreCoupledTightening.changing_write_gas <;> assumption

theorem restore_noop_absent_deletes_non_vacuous_and_tight :
    restoreOf (jsetStep false).1 = .del ∧ sstoreGas true true true = 100 := by
  apply GuestStateRestoreCoupledTightening.noop_absent_deletes <;> assumption

theorem restore_rewrite_sets_non_vacuous_and_tight : restoreOf (jsetStep true).1 = .set := by
  apply GuestStateRestoreCoupledTightening.rewrite_sets <;> assumption

theorem restore_dels_per_call_non_vacuous_and_tight (k : Nat) : delsPerCall k = k := by
  apply GuestStateRestoreCoupledTightening.dels_per_call <;> assumption

theorem restore_dels_vs_units_non_vacuous_and_tight (k c0 n : Nat) :
    n * delsPerCall k + n * c0 = n * (k + c0) := by
  apply GuestStateRestoreCoupledTightening.dels_vs_units <;> assumption

theorem restore_del_bound_refuted_non_vacuous_and_tight : ¬ (1000 * delsPerCall 100 ≤ 0 + 0) := by
  apply GuestStateRestoreCoupledTightening.del_bound_refuted <;> assumption

theorem restore_kPanStateRestoreCoupled_val_non_vacuous_and_tight :
    kPanStateRestoreCoupled = 159893274708 ∧ kPanStateRestoreCoupled = kPanAccessCall := by
  apply GuestStateRestoreCoupledTightening.kPanStateRestoreCoupled_val <;> assumption

theorem restore_slopes_non_vacuous_and_tight :
    5 * kPanStateRestoreCoupled < yukon ∧ yukon < 6 * kPanStateRestoreCoupled := by
  apply GuestStateRestoreCoupledTightening.slopes <;> assumption

theorem restore_hypothetical_fix_non_vacuous_and_tight :
    6 * (136116135658 + 3804281910) < yukon ∧ ¬ (6 * kPanStateRestoreCoupled < yukon) := by
  apply GuestStateRestoreCoupledTightening.hypothetical_fix <;> assumption

theorem al_costs_non_vacuous_and_tight : alAddrGas = 4180 ∧ alKeyGas = 4048 := by
  apply AccessListCallStackAndLabToTargetMaster.al_costs_non_vacuous_and_tight <;> assumption

theorem al_dominated_non_vacuous_and_tight : 26 * 100 < alAddrGas ∧ 21 * 100 < alKeyGas ∧ 20 * 100 < alKeyGas := by
  apply AccessListCallStackAndLabToTargetMaster.al_dominated_non_vacuous_and_tight <;> assumption

theorem al_budget_non_vacuous_and_tight (Kal Aal D A C R W : Nat)
    (h : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2000000) :
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2000000 := by
  apply AccessListCallStackAndLabToTargetMaster.al_budget_non_vacuous_and_tight <;> assumption

theorem undo_eq_non_vacuous_and_tight (d : Nat) : undoTicks d = 5 * d := by
  apply AccessListCallStackAndLabToTargetMaster.undo_eq_non_vacuous_and_tight <;> assumption

theorem revert_eq_non_vacuous_and_tight (l : List (Nat × Nat)) :
    revertCost l = 5 * (l.map (fun p => p.1 * p.2)).sum := by
  apply AccessListCallStackAndLabToTargetMaster.revert_eq_non_vacuous_and_tight <;> assumption

theorem revert_le_non_vacuous_and_tight (l : List (Nat × Nat)) (h : (l.map (fun p => p.1 * p.2)).sum ≤ 3994571428) :
    revertCost l ≤ 19972857140 := by
  apply AccessListCallStackAndLabToTargetMaster.revert_le_non_vacuous_and_tight <;> assumption

theorem truncate_le_non_vacuous_and_tight (c n : Nat) (hc : c ≤ 7989) (hn : n ≤ 95238) :
    5 * c * n ≤ 3804281910 ∧ 21 * 7989 ≤ 167772 ∧ 167772 < 21 * 7990 := by
  apply AccessListCallStackAndLabToTargetMaster.truncate_le_non_vacuous_and_tight <;> assumption

theorem depth_guard_non_vacuous_and_tight (d : Nat) (h : ¬ (d + 1 > 1024)) : d ≤ 1023 := by
  apply AccessListCallStackAndLabToTargetMaster.depth_guard_non_vacuous_and_tight <;> assumption

theorem kPanAccessCall_val_non_vacuous_and_tight : kPanAccessCall = 159893274708 := by
  apply AccessListCallStackAndLabToTargetMaster.kPanAccessCall_val_non_vacuous_and_tight <;> assumption

theorem slopes_non_vacuous_and_tight :
    3 * kPanAccessCall < yukon ∧ 4 * kPanAccessCall < yukon ∧ 5 * kPanAccessCall < yukon ∧
      yukon < 6 * kPanAccessCall := by
  apply AccessListCallStackAndLabToTargetMaster.slopes_non_vacuous_and_tight <;> assumption

theorem threshold_non_vacuous_and_tight (k : Nat) :
    (k * kPanAccessCall < yukon ↔ k ≤ 5) ∧ yukon - 5 * kPanAccessCall = 101253551934 := by
  apply AccessListCallStackAndLabToTargetMaster.threshold_non_vacuous_and_tight <;> assumption

theorem split_local_le_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat)) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) := by
  apply AccessListCallStackAndLabToTargetMaster.split_local_le_non_vacuous_and_tight <;> assumption

theorem split_strict_non_vacuous_and_tight :
    localCost (1, 1, 1, 1, 1) + localCost (1, 1, 1, 1, 1) = 40 ∧ localCost (2, 2, 2, 2, 2) = 80 := by
  apply AccessListCallStackAndLabToTargetMaster.split_strict_non_vacuous_and_tight <;> assumption

theorem prefix_le_non_vacuous_and_tight (l : List (Nat × Nat)) (P : Nat) :
    prefixCost l P ≤ (P + (l.map Prod.fst).sum) * (l.map Prod.snd).sum := by
  apply AccessListCallStackAndLabToTargetMaster.prefix_le_non_vacuous_and_tight <;> assumption

theorem prefix_tight_non_vacuous_and_tight (D W : Nat) : prefixCost [(D, W)] 0 = D * W := by
  apply AccessListCallStackAndLabToTargetMaster.prefix_tight_non_vacuous_and_tight <;> assumption

theorem prefix_strict_non_vacuous_and_tight : prefixCost [(1, 1), (1, 1)] 0 = 3 ∧ 3 < (0 + 2) * 2 := by
  apply AccessListCallStackAndLabToTargetMaster.prefix_strict_non_vacuous_and_tight <;> assumption

theorem reset_bound_non_vacuous_and_tight : 8 * (6 + 1 + (1 + 64 / 32 + 3)) + 2 ≤ txResetTicks := by
  apply AccessListCallStackAndLabToTargetMaster.reset_bound_non_vacuous_and_tight <;> assumption

theorem reset_absorbed_non_vacuous_and_tight (T : Nat) (h : txMinUnits * T ≤ 2000000) :
    txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666 := by
  apply AccessListCallStackAndLabToTargetMaster.reset_absorbed_non_vacuous_and_tight <;> assumption

theorem max_tx_reset_non_vacuous_and_tight : txMinUnits * 16666 ≤ 2000000 ∧ 2000000 < txMinUnits * 16667 ∧
    txResetTicks * 16666 = 3333200 := by
  apply AccessListCallStackAndLabToTargetMaster.max_tx_reset_non_vacuous_and_tight <;> assumption

theorem access_list_key_cost_non_vacuous_and_tight : (2100 - 100) + 128 * 16 = 4048 ∧ 2000 ≤ 4048 := by
  apply AccessListCallStackAndLabToTargetMaster.access_list_key_cost_non_vacuous_and_tight <;> assumption

theorem subblock_master_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat)) (bound : Nat)
    (hb : localCost (sD l, sR l, sA l, sC l, sW l) ≤ bound) :
    (l.map localCost).sum ≤ bound ∧ 6 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables < yukon ∧
      _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables = 136116135658 := by
  apply AccessListCallStackAndLabToTargetMaster.subblock_master_non_vacuous_and_tight <;> assumption

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
  apply AccessListCallStackAndLabToTargetMaster.panToTarget_sections_clean_non_vacuous_and_tight <;> assumption

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
  apply AccessListCallStackAndLabToTargetMaster.panToTarget_sections_length_non_vacuous_and_tight <;> assumption

theorem target_values_non_vacuous_and_tight :
    accessCallSlope3UnrolledK = 479679833456 ∧ accessCallSlope3K = 479679847256 ∧
    accessCallSlope5UnrolledK = 799466382872 ∧ accessCallSlope5K = 799466396672 := by
  apply AccessListCallStackAndLabToTargetMaster.target_values_non_vacuous_and_tight <;> assumption

theorem target_ladder_non_vacuous_and_tight :
    accessCallSlope3UnrolledK < accessCallSlope3K ∧
    accessCallSlope3K < accessCallSlope5UnrolledK ∧
    accessCallSlope5UnrolledK < accessCallSlope5K ∧ accessCallSlope5K < 900719925474 := by
  apply AccessListCallStackAndLabToTargetMaster.target_ladder_non_vacuous_and_tight <;> assumption

theorem target_bounds_non_vacuous_and_tight :
    ∀ k ∈ accessCallTargets, 1212035192 ≤ k ∧ k < yukon := by
  apply AccessListCallStackAndLabToTargetMaster.target_bounds_non_vacuous_and_tight <;> assumption

theorem unrolled_savings_non_vacuous_and_tight :
    accessCallSlope3K - accessCallSlope3UnrolledK = 13800 ∧
    accessCallSlope5K - accessCallSlope5UnrolledK = 13800 := by
  apply AccessListCallStackAndLabToTargetMaster.unrolled_savings_non_vacuous_and_tight <;> assumption

theorem target_margin_non_vacuous_and_tight :
    yukon - accessCallSlope5K = 101253528802 ∧
    yukon - accessCallSlope5UnrolledK = 101253542602 := by
  apply AccessListCallStackAndLabToTargetMaster.target_margin_non_vacuous_and_tight <;> assumption

theorem slope6_rejected_non_vacuous_and_tight :
    yukon < 9332 + 6 * kPanAccessCall := by
  apply AccessListCallStackAndLabToTargetMaster.slope6_rejected_non_vacuous_and_tight <;> assumption

theorem target_one_tick_non_vacuous_and_tight :
    ¬ 9332 + 3 * kPanAccessCall ≤ accessCallSlope3UnrolledK - 1 ∧
    ¬ 23132 + 3 * kPanAccessCall ≤ accessCallSlope3K - 1 ∧
    ¬ 9332 + 5 * kPanAccessCall ≤ accessCallSlope5UnrolledK - 1 ∧
    ¬ 23132 + 5 * kPanAccessCall ≤ accessCallSlope5K - 1 := by
  apply AccessListCallStackAndLabToTargetMaster.target_one_tick_non_vacuous_and_tight <;> assumption

theorem slope3_absorption_non_vacuous_and_tight (post : Nat) (h : post ≤ 3 * kPanAccessCall) :
    9332 + post ≤ accessCallSlope3UnrolledK ∧ 23132 + post ≤ accessCallSlope3K := by
  apply AccessListCallStackAndLabToTargetMaster.slope3_absorption_non_vacuous_and_tight <;> assumption

theorem slope5_absorption_non_vacuous_and_tight (post : Nat) (h : post ≤ 5 * kPanAccessCall) :
    9332 + post ≤ accessCallSlope5UnrolledK ∧ 23132 + post ≤ accessCallSlope5K := by
  apply AccessListCallStackAndLabToTargetMaster.slope5_absorption_non_vacuous_and_tight <;> assumption

theorem portfolio_count_non_vacuous_and_tight : portfolio.length = 40 := by
  apply AccessListCallStackAndLabToTargetMaster.portfolio_count_non_vacuous_and_tight <;> assumption

theorem portfolio_order_non_vacuous_and_tight : portfolio.Pairwise (· < ·) := by
  apply AccessListCallStackAndLabToTargetMaster.portfolio_order_non_vacuous_and_tight <;> assumption

theorem portfolio_coverage_non_vacuous_and_tight :
    (∀ k ∈ MergeTxUnionSixPassMaster.portfolio, k ∈ portfolio) ∧
    (∀ k ∈ accessCallTargets, k ∈ portfolio) := by
  apply AccessListCallStackAndLabToTargetMaster.portfolio_coverage_non_vacuous_and_tight <;> assumption

theorem portfolio_bounds_non_vacuous_and_tight :
    ∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon := by
  apply AccessListCallStackAndLabToTargetMaster.portfolio_bounds_non_vacuous_and_tight <;> assumption

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  apply AccessListCallStackAndLabToTargetMaster.portfolio_certificates_non_vacuous_and_tight <;> assumption

theorem access_list_split_coupled_non_vacuous_and_tight
    (Kal Aal : Nat) (l : List (Nat × Nat × Nat × Nat × Nat))
    (h : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2000000) :
    21 * (sD l + Kal) + 20 * sR l + 26 * (sA l + Aal) + 21 * sC l + sW l ≤ 2000000 ∧
    42 * (l.map localCost).sum ≤ S * S := by
  apply AccessListCallStackAndLabToTargetMaster.access_list_split_coupled_non_vacuous_and_tight <;> assumption

theorem state_restore_envelope_non_vacuous_and_tight
    (probes : List (Nat × Nat)) (c n base : Nat)
    (hp : (probes.map (fun p => p.1 * p.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238) (hb : base ≤ kPanUnifiedAllTables) :
    base + revertCost probes + 5 * c * n ≤ kPanAccessCall := by
  apply AccessListCallStackAndLabToTargetMaster.state_restore_envelope_non_vacuous_and_tight <;> assumption

theorem accessCallSlope3UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK accessCallSlope3UnrolledK) (.finite accessCallSlope3UnrolledK) := by
  apply AccessListCallStackAndLabToTargetMaster.accessCallSlope3UnrolledK_certificate_non_vacuous_and_tight <;> assumption

theorem accessCallSlope3K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK accessCallSlope3K) (.finite accessCallSlope3K) := by
  apply AccessListCallStackAndLabToTargetMaster.accessCallSlope3K_certificate_non_vacuous_and_tight <;> assumption

theorem accessCallSlope5UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK accessCallSlope5UnrolledK) (.finite accessCallSlope5UnrolledK) := by
  apply AccessListCallStackAndLabToTargetMaster.accessCallSlope5UnrolledK_certificate_non_vacuous_and_tight <;> assumption

theorem accessCallSlope5K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK accessCallSlope5K) (.finite accessCallSlope5K) := by
  apply AccessListCallStackAndLabToTargetMaster.accessCallSlope5K_certificate_non_vacuous_and_tight <;> assumption

theorem access_call_lab_to_target_master_non_vacuous_and_tight (arch : AsmArchitecture)
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
    (ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
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
    (∀ k ∈ portfolio, k < yukon ∧ InitE.Certificate (baselineWithFiniteK k) (.finite k)) := by
  apply AccessListCallStackAndLabToTargetMaster.access_call_lab_to_target_master_non_vacuous_and_tight <;> assumption

theorem lab_split_coupled_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat))
    (h : 21*sD l + 20*sR l + 26*sA l + 21*sC l + sW l ≤ S) :
    (l.map localCost).sum + 41935*sR l ≤ 95238095238 := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.split_coupled_non_vacuous_and_tight <;> assumption

theorem lab_split_prefix_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat))
    (p : List (Nat × Nat)) (P : Nat)
    (h : 21*sD l + 20*sR l + 26*sA l + 21*sC l + sW l ≤ S) :
    (l.map localCost).sum + 41935*sR l ≤ 95238095238 ∧
    prefixCost p P ≤ (P + (p.map Prod.fst).sum) * (p.map Prod.snd).sum := by
  apply LabToTargetAndSubBlockThirtySixBudgetMaster.split_prefix_non_vacuous_and_tight <;> assumption

theorem restore_margin_non_vacuous_and_tight :
    yukon = 900719925474 ∧
    yukon - 5 * kPanStateRestoreCoupled = 101253551934 := by decide

theorem forty_certified_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    portfolio.length = 40 ∧ portfolio.Pairwise (· < ·) ∧
    ∀ k ∈ portfolio, k < 900719925474 ∧
      InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  refine ⟨portfolio_count_non_vacuous_and_tight,
    portfolio_order_non_vacuous_and_tight, ?_⟩
  intro k hk
  exact ⟨(portfolio_bounds_non_vacuous_and_tight k hk).2,
    portfolio_certificates_non_vacuous_and_tight cert k hk⟩

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
  exact ⟨access_call_lab_to_target_master_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off
      ic pos labs ffis L' labs' h cert probes c n base hp hc hn hb l Kal Aal hgas,
    restore_dispatch, noop_warm_gas, dels_per_call, del_bound_refuted,
    kPanStateRestoreCoupled_val.1, slopes.1, restore_margin_non_vacuous_and_tight.2⟩

#print axioms restore_restore_dispatch_non_vacuous_and_tight
#print axioms restore_noop_warm_gas_non_vacuous_and_tight
#print axioms restore_changing_write_gas_non_vacuous_and_tight
#print axioms restore_noop_absent_deletes_non_vacuous_and_tight
#print axioms restore_rewrite_sets_non_vacuous_and_tight
#print axioms restore_dels_per_call_non_vacuous_and_tight
#print axioms restore_dels_vs_units_non_vacuous_and_tight
#print axioms restore_del_bound_refuted_non_vacuous_and_tight
#print axioms restore_kPanStateRestoreCoupled_val_non_vacuous_and_tight
#print axioms restore_slopes_non_vacuous_and_tight
#print axioms restore_hypothetical_fix_non_vacuous_and_tight
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
#print axioms access_list_key_cost_non_vacuous_and_tight
#print axioms subblock_master_non_vacuous_and_tight
#print axioms panToTarget_sections_clean_non_vacuous_and_tight
#print axioms panToTarget_sections_length_non_vacuous_and_tight
#print axioms target_values_non_vacuous_and_tight
#print axioms target_ladder_non_vacuous_and_tight
#print axioms target_bounds_non_vacuous_and_tight
#print axioms unrolled_savings_non_vacuous_and_tight
#print axioms target_margin_non_vacuous_and_tight
#print axioms slope6_rejected_non_vacuous_and_tight
#print axioms target_one_tick_non_vacuous_and_tight
#print axioms slope3_absorption_non_vacuous_and_tight
#print axioms slope5_absorption_non_vacuous_and_tight
#print axioms portfolio_count_non_vacuous_and_tight
#print axioms portfolio_order_non_vacuous_and_tight
#print axioms portfolio_coverage_non_vacuous_and_tight
#print axioms portfolio_bounds_non_vacuous_and_tight
#print axioms portfolio_certificates_non_vacuous_and_tight
#print axioms access_list_split_coupled_non_vacuous_and_tight
#print axioms state_restore_envelope_non_vacuous_and_tight
#print axioms accessCallSlope3UnrolledK_certificate_non_vacuous_and_tight
#print axioms accessCallSlope3K_certificate_non_vacuous_and_tight
#print axioms accessCallSlope5UnrolledK_certificate_non_vacuous_and_tight
#print axioms accessCallSlope5K_certificate_non_vacuous_and_tight
#print axioms access_call_lab_to_target_master_non_vacuous_and_tight
#print axioms lab_split_coupled_non_vacuous_and_tight
#print axioms lab_split_prefix_non_vacuous_and_tight
#print axioms restore_margin_non_vacuous_and_tight
#print axioms forty_certified_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.StateRestoreCoupledAndFortyBudgetMaster
