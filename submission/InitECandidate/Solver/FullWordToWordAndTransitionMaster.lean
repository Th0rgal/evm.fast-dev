import InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
import InitECandidate.Solver.GuestSstoreCleanToDirtyTransition
import InitECandidate.Solver.WordSimpAndSstoreCoeffMaster

set_option autoImplicit false
set_option maxRecDepth 200000

/-! Full WordToWord syntactic closure and clean-to-dirty source envelopes.
The arithmetic candidates retain semantic certificate premises; these bounds
alone do not establish a target simulation or certify a changed ROM. -/
namespace InitECandidate.Solver.FullWordToWordAndTransitionMaster
open InitE Flapjack
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver
open WordPassesPreserveNoStoreConsts WordSsaCsePreserveNoStoreConsts
open SelfContainedBoundedCertificate
open _root_.InitECandidate.Solver.GuestSstoreCleanToDirtyTransition (kPanTransition)
open _root_.InitECandidate.Solver.Bs32EnvelopeTwelveCandidateBridge (yukonCeiling)

section Closure
variable {width : Nat} [NeZero width]

theorem fullCompileSingle_non_vacuous_and_tight (b : Bool) (rc alg : Nat)
    (c : AsmConfigExact width) (nm ac : Nat) (p : WordLangProgHOL (BitVec width))
    (co : Option (Spt Nat)) (h : NoSt p = true) :
    NoSt (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.2 = true :=
  WordToWordFullCompileNoStoreConsts.t_fullCompileSingle b rc alg c nm ac p co h

theorem loop_fullCompile_non_vacuous_and_tight (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true :=
  WordToWordFullCompileNoStoreConsts.loopToWord_fullCompileSingle_NoSt ctx q l b rc alg c nm ac co

theorem allowance_non_vacuous_and_tight (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 :=
  WordToWordFullCompileNoStoreConsts.loopToWord_fullCompileSingle_allowance_zero ctx q l b rc alg c nm ac co

theorem fullCompile_list_non_vacuous_and_tight (b : Bool) (rc alg : Nat)
    (c : AsmConfigExact width)
    (ps : List ((Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)))
    (h : ∀ x ∈ ps, NoSt x.1.2.2 = true) :
    ∀ y ∈ ps.map (WordToWord.fullCompileSingle b rc alg c), NoSt y.2.2 = true :=
  WordToWordFullCompileNoStoreConsts.t_fullCompile_list b rc alg c ps h

/-- One integrated statement links full closure, the simp-chain clock, warm
storage coefficients, and the transition envelope without assuming NoSt input. -/
theorem integrated_non_vacuous_and_tight (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac temp k : Nat)
    (co : Option (Spt Nat)) :
    storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 ∧
    SelfContainedMidPassesAndSloadSynth.stackRemoveClockWithAllowance k
      (WordSimpAndSstoreCoeffMaster.simpChain ctx q l c temp ac b) = k + 1 ∧
    GuestSstoreCleanToDirtyTransition.afterSet false = true ∧
    kPanTransition = 135048530896 :=
  ⟨allowance_non_vacuous_and_tight ctx q l b rc alg c nm ac co,
   WordSimpAndSstoreCoeffMaster.stack_clock_non_vacuous_and_tight ctx q l c temp ac b k,
   rfl, GuestSstoreCleanToDirtyTransition.kPanTransition_val.1⟩
end Closure

theorem transition_non_vacuous_and_tight (d : Bool) :
    GuestSstoreCleanToDirtyTransition.afterSet d = true ∧
    GuestSstoreWarmCoeffAudit.cnt .blockStor
      (GuestSstoreWarmCoeffAudit.sstoreWarm (GuestSstoreCleanToDirtyTransition.afterSet d)) = 1 ∧
    GuestSstoreWarmCoeffAudit.cnt .blockStor (GuestSstoreWarmCoeffAudit.sstoreWarm false) = 2 :=
  GuestSstoreCleanToDirtyTransition.transition d

theorem sequence_non_vacuous_and_tight (n : Nat) :
    GuestSstoreCleanToDirtyTransition.seqBlock false (n + 1) = n + 2 ∧
    GuestSstoreCleanToDirtyTransition.seqBlock true n = n :=
  GuestSstoreCleanToDirtyTransition.seqBlock_eq n

theorem block_non_vacuous_and_tight (D W R : Nat)
    (h : 21 * D + W + 20 * R ≤ GuestBs32BlockStorageEnvelope.S) :
    D * (2 * W + 4 * R) ≤ 95238095238 ∧
    47619 * (2 * 1000001 + 4 * 0) = 95238095238 :=
  GuestSstoreCleanToDirtyTransition.block_unchanged D W R h

def transitionSlope3UnrolledK : Nat := 9332 + 3 * kPanTransition
def transitionSlope3K : Nat := 23132 + 3 * kPanTransition
def transitionSlope6UnrolledK : Nat := 9332 + 6 * kPanTransition
def transitionSlope6K : Nat := 23132 + 6 * kPanTransition

theorem values_non_vacuous_and_tight :
    kPanTransition = 135048530896 ∧
    transitionSlope3UnrolledK = 405145602020 ∧ transitionSlope3K = 405145615820 ∧
    transitionSlope6UnrolledK = 810291194708 ∧ transitionSlope6K = 810291208508 := by decide

theorem savings_non_vacuous_and_tight :
    transitionSlope3K - transitionSlope3UnrolledK = 13800 ∧
    transitionSlope6K - transitionSlope6UnrolledK = 13800 := by decide

theorem margin_non_vacuous_and_tight :
    transitionSlope6K < yukonCeiling ∧ yukonCeiling - transitionSlope6K = 90428716966 := by decide

theorem slopes_non_vacuous_and_tight :
    6 * kPanTransition < yukonCeiling ∧ ¬ 7 * kPanTransition < yukonCeiling := by decide

def masterBudgets : List Nat :=
  [1212035192, 2038701869, 11029669988, 11029683788, 19392692330,
   22059330644, 22059344444, 32791963724, 87829684748, 121459456007,
   122620608536, 214346021162, 242918888882, WordSimpAndSstoreCoeffMaster.coupledSlope3K,
   transitionSlope3UnrolledK, transitionSlope3K, 428692019192,
   459244490549, 485837754632, 500060306876, 593385979964, 610978715738,
   610978730738, 677645382458, 677645397458, 775680812618,
   WordSimpAndSstoreCoeffMaster.coupledSlope6K, transitionSlope6UnrolledK, transitionSlope6K,
   857384015252, 857679003380]

theorem full_order_non_vacuous_and_tight :
    (masterBudgets ++ [yukonCeiling]).Pairwise (· < ·) := by decide

theorem count_non_vacuous_and_tight : masterBudgets.length = 31 := by decide

theorem previous_portfolio_non_vacuous_and_tight :
    ∀ k ∈ WordSimpAndSstoreCoeffMaster.masterBudgets, k ∈ masterBudgets := by decide

theorem transition_members_non_vacuous_and_tight :
    transitionSlope3UnrolledK ∈ masterBudgets ∧ transitionSlope3K ∈ masterBudgets ∧
    transitionSlope6UnrolledK ∈ masterBudgets ∧ transitionSlope6K ∈ masterBudgets := by decide

theorem bounds_non_vacuous_and_tight (k : Nat) (hk : k ∈ masterBudgets) :
    1212035192 ≤ k ∧ k < yukonCeiling := by
  simp only [masterBudgets, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem master_certificate_non_vacuous_and_tight (k : Nat) (hk : k ∈ masterBudgets)
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK k) (.finite k) :=
  UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight _ k
    (bounds_non_vacuous_and_tight k hk).1 hc

theorem transitionSlope3UnrolledK_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK transitionSlope3UnrolledK) (.finite transitionSlope3UnrolledK) :=
  master_certificate_non_vacuous_and_tight transitionSlope3UnrolledK (by decide) hc

theorem transitionSlope3K_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK transitionSlope3K) (.finite transitionSlope3K) :=
  master_certificate_non_vacuous_and_tight transitionSlope3K (by decide) hc

theorem transitionSlope6UnrolledK_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK transitionSlope6UnrolledK) (.finite transitionSlope6UnrolledK) :=
  master_certificate_non_vacuous_and_tight transitionSlope6UnrolledK (by decide) hc

theorem transitionSlope6K_certificate_non_vacuous_and_tight
    (hc : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    InitE.Certificate (baselineWithFiniteK transitionSlope6K) (.finite transitionSlope6K) :=
  master_certificate_non_vacuous_and_tight transitionSlope6K (by decide) hc

#print axioms fullCompileSingle_non_vacuous_and_tight
#print axioms loop_fullCompile_non_vacuous_and_tight
#print axioms allowance_non_vacuous_and_tight
#print axioms fullCompile_list_non_vacuous_and_tight
#print axioms integrated_non_vacuous_and_tight
#print axioms transition_non_vacuous_and_tight
#print axioms sequence_non_vacuous_and_tight
#print axioms block_non_vacuous_and_tight
#print axioms values_non_vacuous_and_tight
#print axioms savings_non_vacuous_and_tight
#print axioms margin_non_vacuous_and_tight
#print axioms slopes_non_vacuous_and_tight
#print axioms full_order_non_vacuous_and_tight
#print axioms count_non_vacuous_and_tight
#print axioms previous_portfolio_non_vacuous_and_tight
#print axioms transition_members_non_vacuous_and_tight
#print axioms bounds_non_vacuous_and_tight
#print axioms master_certificate_non_vacuous_and_tight
#print axioms transitionSlope3UnrolledK_certificate_non_vacuous_and_tight
#print axioms transitionSlope3K_certificate_non_vacuous_and_tight
#print axioms transitionSlope6UnrolledK_certificate_non_vacuous_and_tight
#print axioms transitionSlope6K_certificate_non_vacuous_and_tight

end InitECandidate.Solver.FullWordToWordAndTransitionMaster
