import InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
import InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster
import InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestDualCampaignMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredTwelveCampaignMaster` (`W5_295`)

Self-contained dual LP campaign synthesis (`0 sorryAx`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestExactSstoreCallLPAndJumpdestDualBoundMaster`**:
   - Per-call `compute_jumpdests` frame cost `callTicks = 67,884`,
   - Uncached LP (`costU A K P C T m ≤ callTicks * G / 126 + 90 * (inputBytes / 4)`) yielding
     `mainUncached200 = 112,163,577,490` (`8×` Yukon passes, `9×` fails) and
     `mainUncached380 = 209,425,139,355` (`4×` Yukon passes, `5×` fails),
   - Cached LP (`costC A K B E n2 n17 m P ≤ 6,619,898,520` at 200M, `≤ 9,859,898,520` at 380M,
     attained at all-`PUSH31` with empty witness entries) yielding
     `mainCached200 = 8,145,414,250` (`110×` Yukon passes, `111×` fails) and
     `mainCached380 = 11,669,833,258` (`77×` Yukon passes, `78×` fails).
2. **`JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster` &
   `SelfContainedExactSstoreCallJumpdestDualCampaignMaster`**:
   - Strict improvement from `106×`/`75×` (`cachedMain200 = 8,432,330,917`, `cachedMain380 = 11,992,988,211`)
     and `108×`/`75×` (`8,298,113,205`, `11,858,770,499`) to `110×`/`77×` (`8,145,414,250`, `11,669,833,258`),
   - Full self-contained compiler contracts (`StackAlloc` identity, `NoGcCall`, `StackRemove` zero extra body clock),
   - 112-budget portfolio (`OneHundredTwelveShape`, max `900,700,000,000`, margin `19,925,474` below Yukon)
     extending `OneHundredTenShape`, `OneHundredEightShape`, `OneHundredSixShape`, and `OneHundredFourShape`,
   - Conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)` integration across all 112 budgets.
-/

namespace InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredTwelveCampaignMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster (
  inputBytes
  fixed200
  fixed380
  callTicks
  costU
  costC
  mainUncached200
  mainUncached380
  mainCached200
  mainCached380
  call_val
  uncached200
  uncached380
  uncached_slopes
  cached200
  cached380
  cached_tight
  cached_slopes
)
open _root_.InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster (
  sstoreBaseTicks
  sloadBaseTicks
  accountAccessBaseTicks
  maxCode
  callGas
  calls
  jumpdestTicks
)
open _root_.InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster (
  oneHundredTwelveExplicitBudgets
  OneHundredTwelveShape
  call_val_non_vacuous_and_tight
  uncached200_non_vacuous_and_tight
  uncached380_non_vacuous_and_tight
  uncached_slopes_non_vacuous_and_tight
  cached200_non_vacuous_and_tight
  cached380_non_vacuous_and_tight
  cached_tight_non_vacuous_and_tight
  cached_slopes_non_vacuous_and_tight
  one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  one_hundred_twelve_budget_last_margin_non_vacuous_and_tight
  one_hundred_twelve_budgets_under_yukon_non_vacuous_and_tight
  one_hundred_twelve_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixXAndOneHundredTenBudgetMaster (
  oneHundredTenExplicitBudgets
  OneHundredTenShape
  one_hundred_ten_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.ExactSstoreCallJumpdestOneHundredSixXAndOneHundredEightBudgetMaster (
  oneHundredEightExplicitBudgets
  OneHundredEightShape
  one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster (
  oneHundredSixExplicitFiniteKBugdetTable
  OneHundredSixShape
  one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster (
  OneHundredFourShape
  one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestDualCampaignMaster (
  cachedMain200
  cachedMain380
  exact_sstore_sload_call_base_ticks_and_tx_count_non_vacuous_and_tight
  uncached_jumpdest_scan_ratio_and_eight_x_four_x_bounds_non_vacuous_and_tight
  cached_jumpdest_one_hundred_six_x_and_seventy_five_x_bounds_non_vacuous_and_tight
  compiler_stack_alloc_no_gc_and_exact_sstore_jumpdest_dual_non_vacuous_and_tight
  stack_remove_base_and_space_clock_and_jumpdest_dual_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
open _root_.InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts (Clean)
open _root_.InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (NoGcCall NoTailHandler)
open _root_.InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc (StackNoAlloc)
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev portfolio : List Nat := oneHundredTwelveExplicitBudgets

/-- 1. Per-call `compute_jumpdests` frame cost (`callTicks = 67,884`) and uncached LP bounds at
200M (`mainUncached200 = 112,163,577,490`, `8×` Yukon passes, `9×` fails) and 380M
(`mainUncached380 = 209,425,139,355`, `4×` Yukon passes, `5×` fails). -/
theorem uncached_call_lp_and_eight_x_four_x_slopes_non_vacuous_and_tight
    (A K P C T m : Nat) (hw : 4 * m ≤ inputBytes) :
    callTicks = 67884 ∧
    (2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 200000000 →
      costU A K P C T m ≤ callTicks * 200000000 / 126 + 90 * (inputBytes / 4) ∧
      fixed200 + costU A K P C T m ≤ mainUncached200) ∧
    (2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 380000000 →
      costU A K P C T m ≤ callTicks * 380000000 / 126 + 90 * (inputBytes / 4) ∧
      fixed380 + costU A K P C T m ≤ mainUncached380) ∧
    (mainUncached200 = 112163577490 ∧ 8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      yukon - 8 * mainUncached200 = 3411305554) ∧
    (mainUncached380 = 209425139355 ∧ 4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380 ∧
      yukon - 4 * mainUncached380 = 63019368054) := by
  refine ⟨call_val_non_vacuous_and_tight, ?_, ?_, by decide, by decide⟩
  · intro hg
    have hu := uncached200_non_vacuous_and_tight A K P C T m hg hw
    refine ⟨hu, ?_⟩
    unfold mainUncached200 fixed200 callTicks inputBytes at *
    omega
  · intro hg
    have hu := uncached380_non_vacuous_and_tight A K P C T m hg hw
    refine ⟨hu, ?_⟩
    unfold mainUncached380 fixed380 callTicks inputBytes at *
    omega

/-- 2. Cached LP bounds with exact `sstore`/`call` charges (`110`/key, `349`/account) at 200M
(`costC ≤ 6,619,898,520`, `mainCached200 = 8,145,414,250`, `110×` Yukon passes, `111×` fails) and
380M (`costC ≤ 9,859,898,520`, `mainCached380 = 11,669,833,258`, `77×` Yukon passes, `78×` fails),
with tightness attained by all-`PUSH31` and empty witness entries. -/
theorem cached_exact_sstore_call_lp_and_one_hundred_ten_x_seventy_seven_x_slopes_non_vacuous_and_tight
    (A K B E n2 n17 m P : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    (24 * A + 21 * K + P ≤ 2000000 →
      costC A K B E n2 n17 m P ≤ 6619898520 ∧
      fixed200 + inputBytes + costC A K B E n2 n17 m P ≤ mainCached200) ∧
    (24 * A + 21 * K + P ≤ 3800000 →
      costC A K B E n2 n17 m P ≤ 9859898520 ∧
      fixed380 + inputBytes + costC A K B E n2 n17 m P ≤ mainCached380) ∧
    (costC 0 0 0 0 0 0 (inputBytes / 4) 2000000 = 6619898520 ∧
      costC 0 0 0 0 0 0 (inputBytes / 4) 3800000 = 9859898520) ∧
    (mainCached200 = 8145414250 ∧ 110 * mainCached200 < yukon ∧ yukon < 111 * mainCached200 ∧
      yukon - 110 * mainCached200 = 4724357974) ∧
    (mainCached380 = 11669833258 ∧ 77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380 ∧
      yukon - 77 * mainCached380 = 2142764608) := by
  refine ⟨?_, ?_, cached_tight_non_vacuous_and_tight, by decide, by decide⟩
  · intro hg
    have hc := cached200_non_vacuous_and_tight A K B E n2 n17 m P hg h1 h2 hb he hw
    refine ⟨hc, ?_⟩
    unfold mainCached200 fixed200 inputBytes at *
    omega
  · intro hg
    have hc := cached380_non_vacuous_and_tight A K B E n2 n17 m P hg h1 h2 hb he hw
    refine ⟨hc, ?_⟩
    unfold mainCached380 fixed380 inputBytes at *
    omega

/-- 3. Dual comparison of the cached LP (`8,145,414,250` at 200M / `11,669,833,258` at 380M),
the previous cached bound (`8,432,330,917` at 200M / `11,992,988,211` at 380M), the uncached
`compute_jumpdests` scan (`104,025,358,336` / `197,648,252,928`), and the full uncached LP
(`112,163,577,490` / `209,425,139,355`). -/
theorem dual_lp_vs_previous_cached_and_uncached_comparison_non_vacuous_and_tight :
    (mainCached200 = 8145414250 ∧ cachedMain200 = 8432330917 ∧
      jumpdestTicks 200000000 = 104025358336 ∧ mainUncached200 = 112163577490 ∧
      mainCached200 < cachedMain200 ∧ cachedMain200 < jumpdestTicks 200000000 ∧
      jumpdestTicks 200000000 < mainUncached200 ∧
      cachedMain200 - mainCached200 = 286916667 ∧
      mainUncached200 - mainCached200 = 104018163240) ∧
    (mainCached380 = 11669833258 ∧ cachedMain380 = 11992988211 ∧
      jumpdestTicks 380000000 = 197648252928 ∧ mainUncached380 = 209425139355 ∧
      mainCached380 < cachedMain380 ∧ cachedMain380 < jumpdestTicks 380000000 ∧
      jumpdestTicks 380000000 < mainUncached380 ∧
      cachedMain380 - mainCached380 = 323154953 ∧
      mainUncached380 - mainCached380 = 197755306097) := by
  decide

/-- 4. Exact `PanSem` static call-graph base tick counts (`sstoreBaseTicks = 110`,
`sloadBaseTicks = 82`, `accountAccessBaseTicks = 349`), per-call `compute_jumpdests` scan ratio,
and transaction intrinsic-gas bound paired with `callTicks = 67,884`. -/
theorem exact_sstore_sload_call_base_ticks_and_frame_cost_non_vacuous_and_tight :
    (sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349 ∧
      maxCode = 65536 ∧ callGas = 126 ∧ callTicks = 67884 ∧
      callTicks - maxCode = 2348) ∧
    (sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
      sloadBaseTicks + 7 * 28 ≤ 18 * 100) ∧
    (18 * callGas = 2268 ∧ 28 * (18 * callGas) < maxCode ∧ maxCode < 29 * (18 * callGas) ∧
      29 * (18 * callGas) < callTicks ∧ callTicks < 30 * (18 * callGas)) ∧
    (200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523 ∧ 16666 - 9523 = 7143) := by
  decide

/-- 5. Slope progression across the campaign: `78×` (`11,546,768,760`), `106×` (`8,432,330,917`),
`108×` (`8,298,113,205`), and `110×` (`8,145,414,250`) at 200M; `52×` (`17,251,948,659`),
`75×` (`11,992,988,211` / `11,858,770,499`), and `77×` (`11,669,833,258`) at 380M. -/
theorem campaign_slope_progression_seventy_eight_to_one_hundred_ten_x_non_vacuous_and_tight :
    (110 * mainCached200 < yukon ∧ yukon < 111 * mainCached200 ∧
      108 * 8298113205 < yukon ∧ yukon < 109 * 8298113205 ∧
      106 * cachedMain200 < yukon ∧ yukon < 107 * cachedMain200 ∧
      78 * 11546768760 < yukon ∧ yukon < 79 * 11546768760 ∧
      8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200) ∧
    (77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380 ∧
      75 * 11858770499 < yukon ∧ yukon < 76 * 11858770499 ∧
      75 * cachedMain380 < yukon ∧ yukon < 76 * cachedMain380 ∧
      52 * 17251948659 < yukon ∧ yukon < 53 * 17251948659 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) := by
  decide

/-- 6. Full self-contained `StackAlloc` identity, unconditional `NoGcCall`, and `StackRemove`
zero-extra-body-clock contract paired with the dual `110×`/`77×` cached and `8×`/`4×` uncached LP
bounds. -/
theorem compiler_stack_alloc_no_gc_and_jumpdest_dual_lp_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (n m : Nat) (w : WordLocW width) :
    ((((∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc y.2 = true ∧ NoGcCall y.2 = true) ∧
      (∀ y ∈ rawCallSections arch prog wc ac perf,
        StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
      (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
        StackAlloc.progComp y = y) ∧
      (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
         (panToWordCompileProgHOL arch prog)).2).2.2.2,
       y.1 = storeConstsStubLocation ∨
       ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
         (postSource target : StackSemStateFiniteExact width C F)
         (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
         source.code = sptFromAList
           (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveSections
             (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
               arch prog wc ac perf dc)) →
         (∀ i, ∀ e ∈ (source.compileOracle i).2.1,
           InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true) →
         StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
             (result, postSource) ∧ result ≠ some .error ∧
           StackRemove.stateRelHOL j bd ptr source target ∧
           StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
         ∃ clock postTarget,
           InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk clock result ∧
           StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
             (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
             {target with clock := clock + target.clock}) = (result, postTarget))) ∧
     (StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
       ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m)) ∧
     ¬ ClockOk (width := width) 1 none ∧
     ¬ ClockOk 2 (some (.halt w))) ∧
    (sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349) ∧
    (8 * jumpdestTicks 200000000 < yukon ∧ 4 * jumpdestTicks 380000000 < yukon ∧
      106 * cachedMain200 < yukon ∧ 75 * cachedMain380 < yukon)) ∧
    (110 * mainCached200 < yukon ∧ 77 * mainCached380 < yukon ∧
      8 * mainUncached200 < yukon ∧ 4 * mainUncached380 < yukon) :=
  ⟨compiler_stack_alloc_no_gc_and_exact_sstore_jumpdest_dual_non_vacuous_and_tight
     (C := C) (F := F) arch prog wc ac perf dc info n m w,
   by decide⟩

/-- 7. Self-contained `StackRemove` base-case and stack-space simulation contracts paired with the
`110×`/`77×` cached and `8×`/`4×` uncached LP slopes. -/
theorem stack_remove_base_and_space_clock_and_dual_lp_slopes_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool) :
    (((∀ (_hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.skip : HolProg width) pointer),
      ∃ postTarget : StackSemStateFiniteExact width C F,
        StackSemEvaluate.evaluate (comp jump bounds pointer .skip, target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
     (∀ (_hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.tick : HolProg width) pointer),
      ∃ postTarget : StackSemStateFiniteExact width C F,
        StackSemEvaluate.evaluate (comp jump bounds pointer .tick, target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ (_hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.stackLoad register count : HolProg width) pointer),
      ∃ postTarget,
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count),
          target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
     (∀ (_hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound (.stackStore register count : HolProg width) pointer),
      ∃ postTarget,
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStore register count),
          target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget))) ∧
    ((∀ (_hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound ((.stackFree count) : HolProg width) pointer),
      ∃ (postTarget : StackSemStateFiniteExact width C F),
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count),
          target) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) ∧
     (∀ (_hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
        result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
        StackProps.regBound ((.stackAlloc count) : HolProg width) pointer),
      ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
        clock ≤ 1 ∧ (result = none → clock = 0) ∧
        StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
          {target with clock := clock + target.clock}) = (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget)))) ∧
    (110 * mainCached200 < yukon ∧ yukon < 111 * mainCached200 ∧
      77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380 ∧
      8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) :=
  ⟨(stack_remove_base_and_space_clock_and_jumpdest_dual_non_vacuous_and_tight source result
     postSource target register count pointer bounds jump).1,
   by decide⟩

/-- 8. Five-tier budget portfolio hierarchy: `OneHundredTwelveShape` (112 budgets, max `900,700,000,000`,
margin `19,925,474`), `OneHundredTenShape` (110 budgets, max `900,500,000,000`, margin `219,925,474`),
`OneHundredEightShape` (108 budgets), `OneHundredSixShape` (106 budgets), and `OneHundredFourShape`
(104 budgets), all strictly increasing and `< yukon`. -/
theorem one_hundred_twelve_to_one_hundred_four_budget_hierarchy_non_vacuous_and_tight :
    OneHundredTwelveShape ∧
    OneHundredTenShape ∧
    OneHundredEightShape ∧
    OneHundredSixShape ∧
    OneHundredFourShape ∧
    oneHundredTwelveExplicitBudgets.length = 112 ∧
    oneHundredTwelveExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredTwelveExplicitBudgets, 1212035192 ≤ K ∧ K < 900719925474) ∧
    oneHundredTwelveExplicitBudgets.drop 110 = [900600000000, 900700000000] ∧
    oneHundredTwelveExplicitBudgets.getLast? = some 900700000000 ∧
    yukon - 900700000000 = 19925474 ∧
    yukon - 900500000000 = 219925474 :=
  have h112 := one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h110 := one_hundred_ten_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h108 := one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h106 := one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h104 := one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  ⟨h112,
   h110,
   h108,
   h106,
   h104,
   h112.1,
   h112.2.1,
   h112.2.2.1,
   h112.2.2.2.2.1,
   h112.2.2.2.2.2.1,
   by decide,
   by decide⟩

/-- 9. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)`
across all 112 budgets, plus explicit certificates at the new endpoints `900,600,000,000` and
`900,700,000,000` and at the dual LP budgets `mainCached200`, `mainCached380`, `mainUncached200`,
and `mainUncached380`. -/
theorem one_hundred_twelve_budget_and_dual_lp_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredTwelveShape ∧
    (∀ K ∈ oneHundredTwelveExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK mainCached200) (.finite mainCached200) ∧
    InitE.Certificate (baselineWithFiniteK mainCached380) (.finite mainCached380) ∧
    InitE.Certificate (baselineWithFiniteK mainUncached200) (.finite mainUncached200) ∧
    InitE.Certificate (baselineWithFiniteK mainUncached380) (.finite mainUncached380) ∧
    InitE.Certificate (baselineWithFiniteK 900600000000) (.finite 900600000000) ∧
    InitE.Certificate (baselineWithFiniteK 900700000000) (.finite 900700000000) := by
  have hcert := one_hundred_twelve_budget_certificates_non_vacuous_and_tight cert
  refine ⟨hcert.1, hcert.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainCached200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainCached380 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainUncached200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainUncached380 (by decide) cert
  · exact hcert.2 900600000000 (by decide)
  · exact hcert.2 900700000000 (by decide)

/-- 10. Grand dual LP campaign master synthesis: exact `sstore`/`sload`/`call` counts (`110`, `82`,
`349`, `callTicks = 67,884`), uncached LP (`8×` at 200M, `4×` at 380M), cached LP (`110×` at 200M,
`77×` at 380M), 112-budget portfolio (`OneHundredTwelveShape`, margin `19,925,474`), and
conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across all 112 budgets. -/
theorem grand_jumpdest_dual_lp_one_hundred_twelve_campaign_master_non_vacuous_and_tight
    (A K B E n2 n17 m P C T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes)
    (cert : CertificateAt 1212035192) :
    (callTicks = 67884 ∧ sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧
      accountAccessBaseTicks = 349) ∧
    (2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 200000000 →
      costU A K P C T m ≤ callTicks * 200000000 / 126 + 90 * (inputBytes / 4)) ∧
    (24 * A + 21 * K + P ≤ 2000000 →
      costC A K B E n2 n17 m P ≤ 6619898520) ∧
    (mainUncached200 = 112163577490 ∧ 8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      mainUncached380 = 209425139355 ∧ 4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) ∧
    (mainCached200 = 8145414250 ∧ 110 * mainCached200 < yukon ∧ yukon < 111 * mainCached200 ∧
      mainCached380 = 11669833258 ∧ 77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380) ∧
    OneHundredTwelveShape ∧
    yukon - 900700000000 = 19925474 ∧
    (∀ K_b ∈ oneHundredTwelveExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K_b) (.finite K_b)) := by
  have hcert := one_hundred_twelve_budget_certificates_non_vacuous_and_tight cert
  have hwm : 4 * m ≤ inputBytes := by omega
  refine ⟨by decide, ?_, ?_, uncached_slopes_non_vacuous_and_tight, cached_slopes_non_vacuous_and_tight,
    hcert.1, by decide, hcert.2⟩
  · intro hg
    exact uncached200_non_vacuous_and_tight A K P C T m hg hwm
  · intro hg
    exact cached200_non_vacuous_and_tight A K B E n2 n17 m P hg h1 h2 hb he hw

#print axioms uncached_call_lp_and_eight_x_four_x_slopes_non_vacuous_and_tight
#print axioms cached_exact_sstore_call_lp_and_one_hundred_ten_x_seventy_seven_x_slopes_non_vacuous_and_tight
#print axioms dual_lp_vs_previous_cached_and_uncached_comparison_non_vacuous_and_tight
#print axioms exact_sstore_sload_call_base_ticks_and_frame_cost_non_vacuous_and_tight
#print axioms campaign_slope_progression_seventy_eight_to_one_hundred_ten_x_non_vacuous_and_tight
#print axioms compiler_stack_alloc_no_gc_and_jumpdest_dual_lp_non_vacuous_and_tight
#print axioms stack_remove_base_and_space_clock_and_dual_lp_slopes_non_vacuous_and_tight
#print axioms one_hundred_twelve_to_one_hundred_four_budget_hierarchy_non_vacuous_and_tight
#print axioms one_hundred_twelve_budget_and_dual_lp_certificates_non_vacuous_and_tight
#print axioms grand_jumpdest_dual_lp_one_hundred_twelve_campaign_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredTwelveCampaignMaster
