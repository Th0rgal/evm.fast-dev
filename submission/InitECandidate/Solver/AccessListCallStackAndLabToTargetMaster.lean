import InitECandidate.Solver.GuestAccessListAndCallStackDominance
import InitECandidate.Solver.SubBlockTxSplittingAndPanToLabMaster
import InitECandidate.Solver.LabToTargetSectionCleanPreservation

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Access-list and reverted-call arithmetic, transaction splitting, and section-id
preservation through successful label removal. Target budgets are arithmetic
ceilings; certificates explicitly retain the base semantic certificate premise.
No timing simulation of a changed ROM is asserted. -/
namespace InitECandidate.Solver.AccessListCallStackAndLabToTargetMaster

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

variable {width : Nat} [NeZero width]

theorem al_costs_non_vacuous_and_tight : alAddrGas = 4180 ∧ alKeyGas = 4048 := by decide

theorem al_dominated_non_vacuous_and_tight : 26 * 100 < alAddrGas ∧ 21 * 100 < alKeyGas ∧ 20 * 100 < alKeyGas := by decide

theorem al_budget_non_vacuous_and_tight (Kal Aal D A C R W : Nat)
    (h : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2000000) :
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2000000 := by omega

theorem undo_eq_non_vacuous_and_tight (d : Nat) : undoTicks d = 5 * d := by unfold undoTicks; omega

theorem revert_eq_non_vacuous_and_tight (l : List (Nat × Nat)) :
    revertCost l = 5 * (l.map (fun p => p.1 * p.2)).sum := by
  induction l with
  | nil => simp [revertCost]
  | cons x t ih =>
    simp only [revertCost, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, undo_eq]; ring

theorem revert_le_non_vacuous_and_tight (l : List (Nat × Nat)) (h : (l.map (fun p => p.1 * p.2)).sum ≤ 3994571428) :
    revertCost l ≤ 19972857140 := by rw [revert_eq]; omega

theorem truncate_le_non_vacuous_and_tight (c n : Nat) (hc : c ≤ 7989) (hn : n ≤ 95238) :
    5 * c * n ≤ 3804281910 ∧ 21 * 7989 ≤ 167772 ∧ 167772 < 21 * 7990 := by
  refine ⟨?_, by decide, by decide⟩
  have : c * n ≤ 7989 * 95238 := Nat.mul_le_mul hc hn
  calc 5 * c * n = 5 * (c * n) := by ring
    _ ≤ 5 * (7989 * 95238) := by omega
    _ = 3804281910 := by decide

theorem depth_guard_non_vacuous_and_tight (d : Nat) (h : ¬ (d + 1 > 1024)) : d ≤ 1023 := by omega

theorem kPanAccessCall_val_non_vacuous_and_tight : kPanAccessCall = 159893274708 := by decide

theorem slopes_non_vacuous_and_tight :
    3 * kPanAccessCall < yukon ∧ 4 * kPanAccessCall < yukon ∧ 5 * kPanAccessCall < yukon ∧
      yukon < 6 * kPanAccessCall := by decide

theorem threshold_non_vacuous_and_tight (k : Nat) :
    (k * kPanAccessCall < yukon ↔ k ≤ 5) ∧ yukon - 5 * kPanAccessCall = 101253551934 := by
  refine ⟨?_, by decide⟩
  unfold kPanAccessCall kPanUnifiedAllTables
    InitECandidate.Solver.GuestBs32BlockStorageEnvelope.linear
    InitECandidate.Solver.GuestMergeTxUnionEnvelope.locCoup
    InitECandidate.Solver.GuestMergeTxUnionEnvelope.mergeLin yukon
  omega

theorem split_local_le_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat)) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) :=
  GuestSubBlockTxSplittingDominance.split_local_le l

theorem split_strict_non_vacuous_and_tight :
    localCost (1, 1, 1, 1, 1) + localCost (1, 1, 1, 1, 1) = 40 ∧ localCost (2, 2, 2, 2, 2) = 80 :=
  GuestSubBlockTxSplittingDominance.split_strict

theorem prefix_le_non_vacuous_and_tight (l : List (Nat × Nat)) (P : Nat) :
    prefixCost l P ≤ (P + (l.map Prod.fst).sum) * (l.map Prod.snd).sum :=
  GuestSubBlockTxSplittingDominance.prefix_le l P

theorem prefix_tight_non_vacuous_and_tight (D W : Nat) : prefixCost [(D, W)] 0 = D * W :=
  GuestSubBlockTxSplittingDominance.prefix_tight D W

theorem prefix_strict_non_vacuous_and_tight : prefixCost [(1, 1), (1, 1)] 0 = 3 ∧ 3 < (0 + 2) * 2 :=
  GuestSubBlockTxSplittingDominance.prefix_strict

theorem reset_bound_non_vacuous_and_tight : 8 * (6 + 1 + (1 + 64 / 32 + 3)) + 2 ≤ txResetTicks :=
  GuestSubBlockTxSplittingDominance.reset_bound

theorem reset_absorbed_non_vacuous_and_tight (T : Nat) (h : txMinUnits * T ≤ 2000000) :
    txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666 :=
  GuestSubBlockTxSplittingDominance.reset_absorbed T h

theorem max_tx_reset_non_vacuous_and_tight : txMinUnits * 16666 ≤ 2000000 ∧ 2000000 < txMinUnits * 16667 ∧
    txResetTicks * 16666 = 3333200 :=
  GuestSubBlockTxSplittingDominance.max_tx_reset

theorem access_list_key_cost_non_vacuous_and_tight : (2100 - 100) + 128 * 16 = 4048 ∧ 2000 ≤ 4048 :=
  GuestSubBlockTxSplittingDominance.access_list_key_cost

theorem subblock_master_non_vacuous_and_tight (l : List (Nat × Nat × Nat × Nat × Nat)) (bound : Nat)
    (hb : localCost (sD l, sR l, sA l, sC l, sW l) ≤ bound) :
    (l.map localCost).sum ≤ bound ∧ 6 * _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables < yukon ∧
      _root_.InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope.kPanUnifiedAllTables = 136116135658 :=
  GuestSubBlockTxSplittingDominance.split_master l bound hb

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
  have hid : ids L' = ids (StackToLab.compile sc dc mh sp off
      (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2) := by
    rw [ids_removeLabels ic ac pos labs ffis _ L' labs' h, ids_filterSkip]
  refine ⟨?_, ?_⟩
  · rw [hid]; exact stackToLab_compile_ids sc dc mh sp off _
  · intro s' hs'
    obtain ⟨s, hs, he⟩ := mem_of_ids_eq hid s' hs'
    rcases panToLab_sections_unconditional arch prog wc ac perf sc dc mh sp off s hs with st | cl
    · left; rw [← he]; exact st
    · right; exact ⟨s, hs, he, cl⟩

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
  have := congrArg List.length (panToTarget_sections_clean arch prog wc ac perf sc dc mh sp off
    ic pos labs ffis L' labs' h).1
  simp only [ids, List.length_map, List.length_append, List.length_cons, List.length_nil] at this
  omega

def accessCallSlope3UnrolledK : Nat := 9332 + 3 * kPanAccessCall
def accessCallSlope3K : Nat := 23132 + 3 * kPanAccessCall
def accessCallSlope5UnrolledK : Nat := 9332 + 5 * kPanAccessCall
def accessCallSlope5K : Nat := 23132 + 5 * kPanAccessCall

def accessCallTargets : List Nat :=
  [accessCallSlope3UnrolledK, accessCallSlope3K, accessCallSlope5UnrolledK, accessCallSlope5K]

def portfolio : List Nat :=
  (MergeTxUnionSixPassMaster.portfolio ++ accessCallTargets).insertionSort (· ≤ ·)

theorem target_values_non_vacuous_and_tight :
    accessCallSlope3UnrolledK = 479679833456 ∧ accessCallSlope3K = 479679847256 ∧
    accessCallSlope5UnrolledK = 799466382872 ∧ accessCallSlope5K = 799466396672 := by decide

theorem target_ladder_non_vacuous_and_tight :
    accessCallSlope3UnrolledK < accessCallSlope3K ∧
    accessCallSlope3K < accessCallSlope5UnrolledK ∧
    accessCallSlope5UnrolledK < accessCallSlope5K ∧ accessCallSlope5K < 900719925474 := by decide

theorem target_bounds_non_vacuous_and_tight :
    ∀ k ∈ accessCallTargets, 1212035192 ≤ k ∧ k < yukon := by decide

theorem unrolled_savings_non_vacuous_and_tight :
    accessCallSlope3K - accessCallSlope3UnrolledK = 13800 ∧
    accessCallSlope5K - accessCallSlope5UnrolledK = 13800 := by decide

theorem target_margin_non_vacuous_and_tight :
    yukon - accessCallSlope5K = 101253528802 ∧
    yukon - accessCallSlope5UnrolledK = 101253542602 := by decide

theorem slope6_rejected_non_vacuous_and_tight :
    yukon < 9332 + 6 * kPanAccessCall := by decide

theorem target_one_tick_non_vacuous_and_tight :
    ¬ 9332 + 3 * kPanAccessCall ≤ accessCallSlope3UnrolledK - 1 ∧
    ¬ 23132 + 3 * kPanAccessCall ≤ accessCallSlope3K - 1 ∧
    ¬ 9332 + 5 * kPanAccessCall ≤ accessCallSlope5UnrolledK - 1 ∧
    ¬ 23132 + 5 * kPanAccessCall ≤ accessCallSlope5K - 1 := by decide

theorem slope3_absorption_non_vacuous_and_tight (post : Nat) (h : post ≤ 3 * kPanAccessCall) :
    9332 + post ≤ accessCallSlope3UnrolledK ∧ 23132 + post ≤ accessCallSlope3K := by
  unfold accessCallSlope3UnrolledK accessCallSlope3K
  omega

theorem slope5_absorption_non_vacuous_and_tight (post : Nat) (h : post ≤ 5 * kPanAccessCall) :
    9332 + post ≤ accessCallSlope5UnrolledK ∧ 23132 + post ≤ accessCallSlope5K := by
  unfold accessCallSlope5UnrolledK accessCallSlope5K
  omega

theorem portfolio_count_non_vacuous_and_tight : portfolio.length = 40 := by decide

theorem portfolio_order_non_vacuous_and_tight : portfolio.Pairwise (· < ·) := by decide

theorem portfolio_coverage_non_vacuous_and_tight :
    (∀ k ∈ MergeTxUnionSixPassMaster.portfolio, k ∈ portfolio) ∧
    (∀ k ∈ accessCallTargets, k ∈ portfolio) := by decide

theorem portfolio_bounds_non_vacuous_and_tight :
    ∀ k ∈ portfolio, 1212035192 ≤ k ∧ k < yukon := by decide

theorem portfolio_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ portfolio, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  intro k hk
  exact certificate_lift_non_vacuous_and_tight _ _
    (portfolio_bounds_non_vacuous_and_tight k hk).1 hc

theorem access_list_split_coupled_non_vacuous_and_tight
    (Kal Aal : Nat) (l : List (Nat × Nat × Nat × Nat × Nat))
    (h : 40 * Kal + 41 * Aal + 21 * sD l + 20 * sR l + 26 * sA l +
      21 * sC l + sW l ≤ 2000000) :
    21 * (sD l + Kal) + 20 * sR l + 26 * (sA l + Aal) + 21 * sC l + sW l ≤ 2000000 ∧
    42 * (l.map localCost).sum ≤ S * S := by
  refine ⟨al_budget Kal Aal _ _ _ _ _ h, ?_⟩
  apply SubBlockTxSplittingAndPanToLabMaster.split_coupled_envelope_non_vacuous_and_tight
  change 21 * sD l + 20 * sR l + 26 * sA l + 21 * sC l + sW l ≤ 2000000
  omega

theorem state_restore_envelope_non_vacuous_and_tight
    (probes : List (Nat × Nat)) (c n base : Nat)
    (hp : (probes.map (fun p => p.1 * p.2)).sum ≤ 3994571428)
    (hc : c ≤ 7989) (hn : n ≤ 95238) (hb : base ≤ kPanUnifiedAllTables) :
    base + revertCost probes + 5 * c * n ≤ kPanAccessCall := by
  have hr := revert_le probes hp
  have ht := (truncate_le c n hc hn).1
  unfold kPanAccessCall
  omega

theorem accessCallSlope3UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK accessCallSlope3UnrolledK) (.finite accessCallSlope3UnrolledK) :=
  portfolio_certificates_non_vacuous_and_tight hc _ (by decide)

theorem accessCallSlope3K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK accessCallSlope3K) (.finite accessCallSlope3K) :=
  portfolio_certificates_non_vacuous_and_tight hc _ (by decide)

theorem accessCallSlope5UnrolledK_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK accessCallSlope5UnrolledK) (.finite accessCallSlope5UnrolledK) :=
  portfolio_certificates_non_vacuous_and_tight hc _ (by decide)

theorem accessCallSlope5K_certificate_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK accessCallSlope5K) (.finite accessCallSlope5K) :=
  portfolio_certificates_non_vacuous_and_tight hc _ (by decide)

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
  exact ⟨panToTarget_sections_clean_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off
      ic pos labs ffis L' labs' h,
    panToTarget_sections_length_non_vacuous_and_tight arch prog wc ac perf sc dc mh sp off
      ic pos labs ffis L' labs' h,
    state_restore_envelope_non_vacuous_and_tight probes c n base hp hc hn hb,
    (access_list_split_coupled_non_vacuous_and_tight Kal Aal l hgas).2,
    fun k hk => ⟨(portfolio_bounds_non_vacuous_and_tight k hk).2,
      portfolio_certificates_non_vacuous_and_tight cert k hk⟩⟩

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

end InitECandidate.Solver.AccessListCallStackAndLabToTargetMaster
