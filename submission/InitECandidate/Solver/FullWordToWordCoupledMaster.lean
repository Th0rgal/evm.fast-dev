import InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
import InitECandidate.Solver.CoupledTxBlockSixPassTargetCert
import InitECandidate.Solver.SelfContainedFifteenRegimePortfolio

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.FullWordToWordCoupledMaster
open InitE
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open WordPassesPreserveNoStoreConsts StackRemoveStoreConstsZeroBridge
open WordSimpPreservesNoStoreConsts WordToWordFullCompileNoStoreConsts
open SelfContainedMidPassesAndSloadSynth CoupledTxBlockSixPassTargetCert
open UnrolledTwelveCandidatePortfolio SelfContainedBoundedCertificate
open SelfContainedSloadProbeEnvelope
open Flapjack.Pancake.Proofs.PanToTarget

variable {width : Nat} [NeZero width]

theorem full_pass_non_vacuous_and_tight (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat))
    (h : NoSt p = true) :
    NoSt (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.2 = true :=
  t_fullCompileSingle b rc alg c nm ac p co h

theorem loop_full_pass_non_vacuous_and_tight (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true :=
  loopToWord_fullCompileSingle_NoSt ctx q l b rc alg c nm ac co

theorem loop_full_allowance_non_vacuous_and_tight (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 :=
  WordToWordTailNoStoreConstsBridge.noSt_allowance_zero _
    (loopToWord_fullCompileSingle_NoSt ctx q l b rc alg c nm ac co)

theorem loop_full_clock_non_vacuous_and_tight (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac k_sn : Nat)
    (co : Option (Spt Nat)) :
    stackRemoveClockWithAllowance k_sn (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = k_sn + 1 := by
  unfold stackRemoveClockWithAllowance
  rw [loop_full_allowance_non_vacuous_and_tight, Nat.add_zero]

/-- The binary allowance used by the full compiler theorem also vanishes. -/
theorem full_binary_allowance_non_vacuous_and_tight (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    WordSsaCsePreserveNoStoreConsts.storeConstsAllowance
      (WordToWord.fullCompileSingle b rc alg c
        ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 :=
  loopToWord_fullCompileSingle_allowance_zero ctx q l b rc alg c nm ac co

/-- Whole-program output, with origin supplied for every input body. -/
theorem full_list_non_vacuous_and_tight (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (ctx : Spt Nat) (l : Nat × Nat)
    (progs : List ((Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)))
    (origin : ∀ x ∈ progs, ∃ q : HolLoopProg width, x.1.2.2 = (LoopToWord.compHOL ctx q l).1)
    (k_sn : Nat) :
    ∀ y ∈ progs.map (WordToWord.fullCompileSingle b rc alg c),
      NoSt y.2.2 = true ∧ storeConstsAllowance y.2.2 = 0 ∧
      stackRemoveClockWithAllowance k_sn y.2.2 = k_sn + 1 := by
  have hinput : ∀ x ∈ progs, NoSt x.1.2.2 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := origin x hx
    rw [hq]; exact loopToWord_NoSt ctx q l
  intro y hy
  have hn := t_fullCompile_list b rc alg c progs hinput y hy
  have hz : storeConstsAllowance y.2.2 = 0 :=
    WordToWordTailNoStoreConstsBridge.noSt_allowance_zero _ hn
  exact ⟨hn, hz, by simp [stackRemoveClockWithAllowance, hz]⟩

/-- Sorted union of both imported portfolios, including all SLOAD and bs32 regimes. -/
def unified : List Nat :=
  fullCandidates.take 13 ++
  [Bs32DominanceSixPassTargetCert.bs32StandaloneSlope3K,
   Bs32DominanceSixPassTargetCert.bs32TotalSlope3K, coupledTxBlockSlope3K,
   BlockVsTxSixPassTargetCert.blockVsTxSlope6K,
   Bs32EnvelopeTwelveCandidateBridge.bs32JointSlope3K,
   JointBlockGasSixPassMasterCert.jointBlockGasSlope12K,
   Bs32EnvelopeTwelveCandidateBridge.bs32SumSlope3K,
   Bs32DominanceSixPassTargetCert.bs32StandaloneSlope6K,
   coldSloadProbeZeroOffsetK, coldSloadProbeEnvelopeTargetK,
   sloadProbeZeroOffsetK, sloadProbeEnvelopeTargetK,
   Bs32DominanceSixPassTargetCert.bs32TotalSlope6K, coupledTxBlockSlope6K, terminalK]

theorem unified_order_non_vacuous_and_tight : unified.Pairwise (· < ·) := by decide

theorem unified_count_non_vacuous_and_tight : unified.length = 28 := by decide

theorem unified_coverage_non_vacuous_and_tight :
    (∀ k ∈ fullCandidates, k ∈ unified) ∧
    (∀ k ∈ SelfContainedFifteenRegimePortfolio.allTwentyFourRegimes, k ∈ unified) ∧
    (∀ k ∈ SelfContainedFifteenRegimePortfolio.fifteenPrincipalRegimes, k ∈ unified) := by decide

theorem unified_bounds_non_vacuous_and_tight :
    ∀ k ∈ unified, 1212035192 ≤ k ∧ k < 900719925474 := by decide

theorem coupled_values_non_vacuous_and_tight :
    coupledTxBlockSlope3K = 392562715820 ∧ coupledTxBlockSlope6K = 785125408508 ∧
    coupledTxBlockSlope3K < coupledTxBlockSlope6K ∧ coupledTxBlockSlope6K < 900719925474 := by decide

theorem unified_one_tick_non_vacuous_and_tight (k : Nat) (hk : k ∈ unified) :
    ¬ k ≤ k - 1 := by
  have h := (unified_bounds_non_vacuous_and_tight k hk).1
  omega

theorem unified_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ unified, InitE.Certificate (baselineWithFiniteK k) (.finite k) := by
  intro k hk
  exact certificate_lift_non_vacuous_and_tight _ _
    (unified_bounds_non_vacuous_and_tight k hk).1 hc

theorem coupled_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK coupledTxBlockSlope3K) (.finite coupledTxBlockSlope3K) ∧
    InitE.Certificate (baselineWithFiniteK coupledTxBlockSlope6K) (.finite coupledTxBlockSlope6K) :=
  ⟨certificate_lift_non_vacuous_and_tight _ _ (by decide) hc,
   certificate_lift_non_vacuous_and_tight _ _ (by decide) hc⟩

theorem fifteen_certificates_non_vacuous_and_tight (hc : CertificateAt 1212035192) :
    ∀ k ∈ SelfContainedFifteenRegimePortfolio.fifteenPrincipalRegimes, CertificateAt k :=
  (SelfContainedFifteenRegimePortfolio.master_fifteen_and_twenty_four_regime_certificate_selection_non_vacuous_and_tight hc).1

theorem slope_threshold_non_vacuous_and_tight (slope : Nat) :
    bootstrapSteps + slope * GuestCoupledTxBlockStorageBound.kPanCoupled < yukonCeiling ↔ slope ≤ 6 :=
  threshold_non_vacuous_and_tight slope

/-- Compiler invariants are unconditional; target certificates retain their semantic premise.
`C_sr = 1` is the coefficient of `k_sn` in the proved clock equation. -/
theorem full_word_to_word_coupled_master_non_vacuous_and_tight
    (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat) (b : Bool)
    (rc alg : Nat) (c : AsmConfigExact width) (nm ac k_sn : Nat) (co : Option (Spt Nat))
    (hc : CertificateAt 1212035192) :
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true ∧
    storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 ∧
    stackRemoveClockWithAllowance k_sn (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 1 * k_sn + 1 ∧
    unified.Pairwise (· < ·) ∧
    (∀ k ∈ unified, InitE.Certificate (baselineWithFiniteK k) (.finite k)) := by
  exact ⟨loop_full_pass_non_vacuous_and_tight ctx q l b rc alg c nm ac co,
    loop_full_allowance_non_vacuous_and_tight ctx q l b rc alg c nm ac co,
    by simpa using loop_full_clock_non_vacuous_and_tight ctx q l b rc alg c nm ac k_sn co,
    unified_order_non_vacuous_and_tight, unified_certificates_non_vacuous_and_tight hc⟩

#print axioms full_pass_non_vacuous_and_tight
#print axioms loop_full_pass_non_vacuous_and_tight
#print axioms loop_full_allowance_non_vacuous_and_tight
#print axioms loop_full_clock_non_vacuous_and_tight
#print axioms full_binary_allowance_non_vacuous_and_tight
#print axioms full_list_non_vacuous_and_tight
#print axioms unified_order_non_vacuous_and_tight
#print axioms unified_count_non_vacuous_and_tight
#print axioms unified_coverage_non_vacuous_and_tight
#print axioms unified_bounds_non_vacuous_and_tight
#print axioms coupled_values_non_vacuous_and_tight
#print axioms unified_one_tick_non_vacuous_and_tight
#print axioms unified_certificates_non_vacuous_and_tight
#print axioms coupled_certificates_non_vacuous_and_tight
#print axioms fifteen_certificates_non_vacuous_and_tight
#print axioms slope_threshold_non_vacuous_and_tight
#print axioms full_word_to_word_coupled_master_non_vacuous_and_tight
end InitECandidate.Solver.FullWordToWordCoupledMaster
