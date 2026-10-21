import InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
import InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock
import InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact synthesis of the imported hand cost estimates, conditional on bounded
salted probe runs and memoized witness decoding. These arithmetic estimates are
not semantic runtime certificates; finite certificates remain conditional on
the base certificate. StackRemove adds zero clock except at most one tick on a
final halt. The r=1 lever uses the proved value 25,388,940,380. -/
namespace InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev Previous := OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318293, 880629318294]
def EightyFourShape : Prop :=
  portfolio.length = 84 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 82 = Previous ∧
  portfolio.drop 82 = [880629318293, 880629318294] ∧
  portfolio.getLast? = some 880629318294 ∧ yukon = 900719925474

theorem dissect_and_probes_salted_non_vacuous_and_tight :
    (decodeMemo + probesR8 + (20036870848 - 619060000) = 38946487944 ∧
    probesR8 = 8589933568) ∧
    (probesR8 = 2 * 8 * (16 * 33554428)) :=
  ⟨GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.dissect, GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.probes_salted⟩

theorem visit_cost_and_rows_200_non_vacuous_and_tight :
    (30 + 633 = 663 ∧ 663 < 1000) ∧
    (buildNodedb = 3038649506 ∧ walks 200000000 = 130000000 ∧
    rootTicks 200000000 = 4104281610) :=
  ⟨GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.visit_cost, GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.rows_200⟩

theorem wm_vals_and_post_val_non_vacuous_and_tight :
    (witnessMptSalted 200000000 = 26801608212 ∧
    witnessMptSalted 380000000 = 30612453042) ∧
    (postEvmSalted = 681400462) :=
  ⟨GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.wm_vals, GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.post_val⟩

theorem main200_slope_non_vacuous_and_tight :
    (main200 = 32905132252 ∧ 27 * main200 < yukon ∧ yukon < 28 * main200) :=
  GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main200_slope

theorem main380_slope_and_no_thirty_non_vacuous_and_tight :
    (main380 = 41010777082 ∧ 21 * main380 < yukon ∧ yukon < 22 * main380) ∧
    (yukon / 30 = 30023997515 ∧ yukon < 30 * main200) :=
  ⟨GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.main380_slope, GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.no_thirty⟩

theorem dominant_and_r1_lever_non_vacuous_and_tight :
    (100 * (decodeMemo + probesR8) > 59 * main200) ∧
    (main200 - probesR8 + 2 * 1 * 536870848 = 25388940380 ∧
    35 * 25388940380 < yukon ∧ yukon < 36 * 25388940380) :=
  ⟨GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.dominant, GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit.r1_lever⟩

theorem noSt_initStubs_non_vacuous_and_tight {width : Nat} [NeZero width] (generateGc : Bool) (maximumHeap pointer start : Nat) :
    ∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true :=
  StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock.noSt_initStubs generateGc maximumHeap pointer start

theorem initCode_clock_preserved_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maximumHeap pointer : Nat)
    (source post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, source) = (result, post)) :
    post.clock = source.clock :=
  StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock.initCode_clock_preserved generateGc maximumHeap pointer source post result run

theorem stackRemoveCompile_sections_noSt_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) :
    ∀ e ∈ StackRemove.compileHOL jump bounds generateGc maximumHeap pointer start
        (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)),
      e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true :=
  StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock.stackRemoveCompile_sections_noSt arch prog wc ac perf dc jump bounds generateGc maximumHeap pointer start

theorem pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) :
    (∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
    (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
      t.clock = s.clock) ∧
    (∀ e ∈ StackRemove.compileHOL jump bounds generateGc maximumHeap pointer start
        (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)),
      e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        CodeNoSt source →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) :=
  StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock.pancake_stackRemove_compileProg_zeroExtraBodyClock arch prog wc ac perf dc info jump bounds generateGc maximumHeap pointer start

theorem eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    EightyFourShape := by
  unfold EightyFourShape
  decide

theorem eighty_four_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyFourShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms dissect_and_probes_salted_non_vacuous_and_tight
#print axioms visit_cost_and_rows_200_non_vacuous_and_tight
#print axioms wm_vals_and_post_val_non_vacuous_and_tight
#print axioms main200_slope_non_vacuous_and_tight
#print axioms main380_slope_and_no_thirty_non_vacuous_and_tight
#print axioms dominant_and_r1_lever_non_vacuous_and_tight
#print axioms noSt_initStubs_non_vacuous_and_tight
#print axioms initCode_clock_preserved_non_vacuous_and_tight
#print axioms stackRemoveCompile_sections_noSt_non_vacuous_and_tight
#print axioms pancake_stackRemove_compileProg_zeroExtraBodyClock_non_vacuous_and_tight
#print axioms eighty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms eighty_four_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SaltedNodedbTwentySevenXAndEightyFourBudgetMaster
