import InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
import InitECandidate.Solver.SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth
import InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixXAndOneHundredEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_293: self-contained jumpdest dual LP (uncached 8x/4x and cached 110x/77x)
with global gas-coupled LP arithmetic, full compiler contracts and 108 conditional
finite certificates. Joint bounds retain every gas, dirty-node and witness-byte
hypothesis. The cached model requires a per-code jumpdest cache. Finite
certificates remain conditional on the base semantic certificate. -/
namespace InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredEightBudgetSynth

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
open _root_.InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster
  (cost main200 main380)
open _root_.InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
  (inputBytes fixed200 fixed380 callTicks costU costC
   mainUncached200 mainUncached380 mainCached200 mainCached380)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev oneHundredSixExplicitFiniteKBugdetTable :=
  GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster.oneHundredSixExplicitFiniteKBugdetTable

abbrev oneHundredEightExplicitFiniteKBugdetTable :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredEightBudgetMaster.oneHundredEightExplicitBudgets

abbrev portfolio := oneHundredEightExplicitFiniteKBugdetTable

abbrev OneHundredSixShape :=
  GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster.OneHundredSixShape

abbrev OneHundredEightShape :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredEightBudgetMaster.OneHundredEightShape

/-- 1. Per-call ticks (`67,884`) and fixed rows (`1,391,298,018` at 200M, `1,675,717,026` at 380M). -/
theorem call_val_and_fixed_vals_non_vacuous_and_tight :
    callTicks = 67884 ∧ fixed200 = 1391298018 ∧ fixed380 = 1675717026 :=
  ⟨GuestExactSstoreCallLPAndJumpdestDualBoundMaster.call_val,
   SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth.fixed_vals_and_all_push_non_vacuous_and_tight.1⟩

/-- 2. Uncached joint bound at 200M gas. -/
theorem uncached200_non_vacuous_and_tight (A K P C T m : Nat)
    (hg : 2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 200000000) (hw : 4 * m ≤ inputBytes) :
    costU A K P C T m ≤ callTicks * 200000000 / 126 + 90 * (inputBytes / 4) :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.uncached200 A K P C T m hg hw

/-- 3. Uncached joint bound at 380M gas. -/
theorem uncached380_non_vacuous_and_tight (A K P C T m : Nat)
    (hg : 2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 380000000) (hw : 4 * m ≤ inputBytes) :
    costU A K P C T m ≤ callTicks * 380000000 / 126 + 90 * (inputBytes / 4) :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.uncached380 A K P C T m hg hw

/-- 4. Uncached Guest slopes: `8x` at 200M and `4x` at 380M. -/
theorem uncached_slopes_non_vacuous_and_tight :
    mainUncached200 = 112163577490 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 209425139355 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.uncached_slopes

/-- 5. Cached joint LP (`costC ≤ 6,619,898,520`) and global joint LP (`3 * cost ≤ 20,720,445,560`) at 200M. -/
theorem cached200_and_joint200_non_vacuous_and_tight (A K B E n2 n17 m P : Nat)
    (hg : 24 * A + 21 * K + P ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    costC A K B E n2 n17 m P ≤ 6619898520 ∧
    3 * cost A K B E n2 n17 m P ≤ 20720445560 :=
  ⟨GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached200 A K B E n2 n17 m P hg h1 h2 hb he hw,
   SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth.joint200_non_vacuous_and_tight A K B E n2 n17 m P hg h1 h2 hb he hw⟩

/-- 6. Cached joint LP (`costC ≤ 9,859,898,520`) and global joint LP (`65 * cost ≤ 661,898,475,728`) at 380M. -/
theorem cached380_and_joint380_non_vacuous_and_tight (A K B E n2 n17 m P : Nat)
    (hg : 24 * A + 21 * K + P ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    costC A K B E n2 n17 m P ≤ 9859898520 ∧
    65 * cost A K B E n2 n17 m P ≤ 661898475728 :=
  ⟨GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached380 A K B E n2 n17 m P hg h1 h2 hb he hw,
   SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth.joint380_non_vacuous_and_tight A K B E n2 n17 m P hg h1 h2 hb he hw⟩

/-- 7. Optimum attainment for `costC` (all PUSH31, empty witness entries) and `cost` at 200M. -/
theorem cached_tight_and_all_push_non_vacuous_and_tight :
    (costC 0 0 0 0 0 0 (inputBytes / 4) 2000000 = 6619898520 ∧
      costC 0 0 0 0 0 0 (inputBytes / 4) 3800000 = 9859898520) ∧
    3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560 :=
  ⟨GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached_tight,
   SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth.fixed_vals_and_all_push_non_vacuous_and_tight.2⟩

/-- 8. Cached Guest slopes (`110x` at 200M, `77x` at 380M) and global LP slopes (`108x` at 200M, `75x` at 380M). -/
theorem cached_slopes_and_global_slopes_non_vacuous_and_tight :
    (mainCached200 = 8145414250 ∧ 110 * mainCached200 < yukon ∧
      yukon < 111 * mainCached200 ∧ mainCached380 = 11669833258 ∧ 77 * mainCached380 < yukon ∧
      yukon < 78 * mainCached380) ∧
    (main200 = 8298113205 ∧ 108 * main200 < yukon ∧ yukon < 109 * main200 ∧
      main200 < 9000000000) ∧
    (main380 = 11858770499 ∧ 75 * main380 < yukon ∧ yukon < 76 * main380) :=
  ⟨GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached_slopes,
   SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth.main200_slope_non_vacuous_and_tight,
   SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth.main380_slope_non_vacuous_and_tight⟩

/-- 9. Exact margins below Yukon (`110x`/`77x` cached and `108x`/`75x` global) plus sensitivity. -/
theorem margins_and_sensitivity_non_vacuous_and_tight :
    (yukon - 110 * mainCached200 = 4724357974 ∧ yukon - 77 * mainCached380 = 2142764608) ∧
    (yukon - 108 * main200 = 4523699334 ∧ yukon - 75 * main380 = 11312138049) ∧
    (98 * 9131446538 < yukon ∧ yukon < 99 * 9131446538) ∧
    (mainCached200 < main200 ∧ main200 - mainCached200 = 152698955 ∧
      mainCached380 < main380 ∧ main380 - mainCached380 = 188937241) := by
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
  SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth.user_sections_base_cases_stack_space_non_vacuous_and_tight

/-- 11. Exactly 108 increasing finite budgets below Yukon (`[896500000000, 898500000000]`, margin `2219925474`). -/
theorem one_hundred_eight_budget_table_non_vacuous_and_tight :
    OneHundredEightShape ∧ OneHundredSixShape ∧
    oneHundredEightExplicitFiniteKBugdetTable.length = 108 ∧
    oneHundredEightExplicitFiniteKBugdetTable.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredEightExplicitFiniteKBugdetTable, K < 900719925474) ∧
    oneHundredEightExplicitFiniteKBugdetTable.drop 106 = [896500000000, 898500000000] ∧
    oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
    oneHundredEightExplicitFiniteKBugdetTable.getLast? = some 898500000000 ∧
    yukon - 898500000000 = 2219925474 := by
  refine ⟨ExactSstoreCallJumpdestOneHundredSixXAndOneHundredEightBudgetMaster.one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
    SelfContainedGlobalGasCoupledOneHundredSixBudgetSynth.one_hundred_six_budget_table_non_vacuous_and_tight.1, ?_⟩
  decide

/-- 12. Conditional finite certificates across all 108 budgets. -/
theorem one_hundred_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredEightShape ∧
    (∀ K ∈ oneHundredEightExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ExactSstoreCallJumpdestOneHundredSixXAndOneHundredEightBudgetMaster.one_hundred_eight_budget_certificates_non_vacuous_and_tight cert

#print axioms call_val_and_fixed_vals_non_vacuous_and_tight
#print axioms uncached200_non_vacuous_and_tight
#print axioms uncached380_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms cached200_and_joint200_non_vacuous_and_tight
#print axioms cached380_and_joint380_non_vacuous_and_tight
#print axioms cached_tight_and_all_push_non_vacuous_and_tight
#print axioms cached_slopes_and_global_slopes_non_vacuous_and_tight
#print axioms margins_and_sensitivity_non_vacuous_and_tight
#print axioms user_sections_base_cases_stack_space_non_vacuous_and_tight
#print axioms one_hundred_eight_budget_table_non_vacuous_and_tight
#print axioms one_hundred_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredEightBudgetSynth
