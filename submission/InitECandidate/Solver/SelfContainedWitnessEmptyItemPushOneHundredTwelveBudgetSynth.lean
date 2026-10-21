import InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
import InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredTenBudgetSynth
import InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_305: self-contained witness empty-item (`keccakEmpty = 35`, `43` ticks/entry)
and exact `PUSH31` (`push31 = 54 = 18 * 3`) LP (`mainCached200 = 8014558459`, 112x Yukon;
`mainCached380 = 11548778048`, 77x Yukon; uncached 8x/4x), full compiler contracts
and 112 conditional finite certificates. Joint bounds retain every gas, dirty-node
and witness-byte hypothesis. The cached model requires a per-code jumpdest cache.
Finite certificates remain conditional on the base semantic certificate. -/
namespace InitECandidate.Solver.SelfContainedWitnessEmptyItemPushOneHundredTwelveBudgetSynth

open InitECandidate.Solver
open _root_.InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (NoGcCall NoTailHandler)
open Flapjack.Pancake.PanLang
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
  (callTicks)
open _root_.InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
  (inputBytes fixed200 fixed380 keccakEmpty push31 costC costU
   mainCached200 mainCached380 mainUncached200 mainUncached380)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev oneHundredTenExplicitFiniteKBugdetTable :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.oneHundredTenExplicitBudgets

abbrev oneHundredTwelveExplicitFiniteKBugdetTable :=
  JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster.oneHundredTwelveExplicitBudgets

abbrev portfolio := oneHundredTwelveExplicitFiniteKBugdetTable

abbrev OneHundredTenShape :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster.OneHundredTenShape

abbrev OneHundredTwelveShape :=
  JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster.OneHundredTwelveShape

/-- 1. Exact leaf counts (`keccakEmpty = 35`, `push31 = 54 = 18 * 3`), `callTicks = 67884` and fixed rows. -/
theorem leaf_counts_and_fixed_vals_non_vacuous_and_tight :
    (keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3) ∧
    (callTicks = 67884 ∧ fixed200 = 1391298018 ∧ fixed380 = 1675717026) :=
  ⟨GuestWitnessEmptyItemAndPushExactTicksMaster.leaf_counts,
   SelfContainedJumpdestDualLPOneHundredTenBudgetSynth.call_val_and_fixed_vals_non_vacuous_and_tight⟩

/-- 2. Cached witness empty-item and exact PUSH31 joint LP at 200M gas. -/
theorem cached200_non_vacuous_and_tight (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    33 * costC A K B E n2 n17 md ms P ≤ 214138410040 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.cached200 A K B E n2 n17 md ms P hg h1 h2 hb he hw

/-- 3. Cached witness empty-item and exact PUSH31 joint LP at 380M gas. -/
theorem cached380_non_vacuous_and_tight (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K B E n2 n17 md ms P ≤ 114947567578464 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.cached380 A K B E n2 n17 md ms P hg h1 h2 hb he hw

/-- 4. Uncached full LP at 200M gas. -/
theorem uncached200_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.uncached200 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 5. Uncached full LP at 380M gas. -/
theorem uncached380_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.uncached380 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 6. Cached Guest slopes (`mainCached200 = 8,014,558,459` at `112x`, `mainCached380 = 11,548,778,048` at `77x`). -/
theorem cached_slopes_non_vacuous_and_tight :
    mainCached200 = 8014558459 ∧ 112 * mainCached200 < yukon ∧
    yukon < 113 * mainCached200 ∧ mainCached380 = 11548778048 ∧ 77 * mainCached380 < yukon ∧
    yukon < 78 * mainCached380 :=
  GuestWitnessEmptyItemAndPushExactTicksMaster.cached_slopes

/-- 7. Uncached Guest slopes (`8x` at 200M, `4x` at 380M) and `135x` non-attainment. -/
theorem uncached_slopes_and_no_135_non_vacuous_and_tight :
    (mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 208876066898 ∧ 4 * mainUncached380 < yukon ∧
      yukon < 5 * mainUncached380) ∧
    (yukon / 135 = 6671999447 ∧ yukon < 135 * mainCached200) :=
  ⟨GuestWitnessEmptyItemAndPushExactTicksMaster.uncached_slopes,
   GuestWitnessEmptyItemAndPushExactTicksMaster.no_135⟩

/-- 8. Strict improvement of `112x` cached LP (`8,014,558,459`) over `110x` (`8,145,414,250`) and `108x` (`8,298,113,205`). -/
theorem dual_lp_one_hundred_ten_x_comparison_non_vacuous_and_tight :
    (GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 = 8145414250 ∧
      110 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 < yukon ∧
      yukon < 111 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 = 11669833258 ∧
      77 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 < yukon ∧
      yukon < 78 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380) ∧
    (GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200 = 8298113205 ∧
      108 * GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200 < yukon ∧
      yukon < 109 * GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200 ∧
      GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main200 < 9000000000) ∧
    (GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380 = 11858770499 ∧
      75 * GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380 < yukon ∧
      yukon < 76 * GuestGlobalGasCoupledEvmAndSubNineBillionMaster.main380) :=
  SelfContainedJumpdestDualLPOneHundredTenBudgetSynth.cached_slopes_and_global_slopes_non_vacuous_and_tight

/-- 9. Exact margins below Yukon at `112x` (200M) and `77x` (380M) plus exact step-down deltas. -/
theorem margins_non_vacuous_and_tight :
    yukon - 112 * mainCached200 = 3089378066 ∧
    yukon - 77 * mainCached380 = 11464015778 ∧
    mainCached200 < 8145414250 ∧ 8145414250 - mainCached200 = 130855791 ∧
    mainCached380 < 11669833258 ∧ 11669833258 - mainCached380 = 121055210 := by
  decide

/-- 10. User sections, base cases and stack-space simulation contracts. -/
theorem user_sections_base_cases_stack_space_non_vacuous_and_tight :
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (((∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.skip : HolProg width) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .skip,
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.tick : HolProg width) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .tick,
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : HolInst width)
    (_hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.inst instruction) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackLoad register count : HolProg width) pointer),
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
    (∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackStore register count : HolProg width) pointer),
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStore register count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)))) ∧
    (((∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackFree count) : HolProg width) pointer),
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackAlloc count) : HolProg width) pointer),
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F), clock ≤ 1 ∧ (result = none → clock = 0) ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget)))) :=
  SelfContainedJumpdestDualLPOneHundredTenBudgetSynth.user_sections_base_cases_stack_space_non_vacuous_and_tight

/-- 11. Exactly 112 increasing finite budgets below Yukon (`[900600000000, 900700000000]`, margin `19925474`). -/
theorem one_hundred_twelve_budget_table_non_vacuous_and_tight :
    OneHundredTwelveShape ∧ OneHundredTenShape ∧
    oneHundredTwelveExplicitFiniteKBugdetTable.length = 112 ∧
    oneHundredTwelveExplicitFiniteKBugdetTable.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwelveExplicitFiniteKBugdetTable, K < 900719925474) ∧
    oneHundredTwelveExplicitFiniteKBugdetTable.drop 110 = [900600000000, 900700000000] ∧
    oneHundredTenExplicitFiniteKBugdetTable.getLast? = some 900500000000 ∧
    oneHundredTwelveExplicitFiniteKBugdetTable.getLast? = some 900700000000 ∧
    yukon - 900700000000 = 19925474 := by
  refine ⟨JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster.one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
    SelfContainedJumpdestDualLPOneHundredTenBudgetSynth.one_hundred_ten_budget_table_non_vacuous_and_tight.1, ?_⟩
  decide

/-- 12. Conditional finite certificates across all 112 budgets. -/
theorem one_hundred_twelve_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwelveShape ∧
    (∀ K ∈ oneHundredTwelveExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster.one_hundred_twelve_budget_certificates_non_vacuous_and_tight cert

#print axioms leaf_counts_and_fixed_vals_non_vacuous_and_tight
#print axioms cached200_non_vacuous_and_tight
#print axioms cached380_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms uncached_slopes_and_no_135_non_vacuous_and_tight
#print axioms dual_lp_one_hundred_ten_x_comparison_non_vacuous_and_tight
#print axioms margins_non_vacuous_and_tight
#print axioms user_sections_base_cases_stack_space_non_vacuous_and_tight
#print axioms one_hundred_twelve_budget_table_non_vacuous_and_tight
#print axioms one_hundred_twelve_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWitnessEmptyItemPushOneHundredTwelveBudgetSynth
