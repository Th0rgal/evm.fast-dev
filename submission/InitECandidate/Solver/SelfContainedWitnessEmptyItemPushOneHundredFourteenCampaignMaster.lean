import InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
import InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster
import InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredTwelveCampaignMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedWitnessEmptyItemPushOneHundredFourteenCampaignMaster` (`W5_304`)

Self-contained dual LP campaign synthesis (`0 sorryAx`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestWitnessEmptyItemAndPushExactTicksMaster`**:
   - Exact leaf counts (`keccakEmpty = 35`, `push31 = 54 = 18 * 3`, `leaf_counts`),
   - Cached full LP (`33 * costC ≤ 214,138,410,040` at 200M, `11803 * costC ≤ 114,947,567,578,464` at 380M)
     yielding `mainCached200 = 8,014,558,459` (`112×` Yukon passes, `113×` fails) and
     `mainCached380 = 11,548,778,048` (`77×` Yukon passes, `78×` fails), with `no_135`,
   - Uncached full LP (`231 * costU ≤ 25,461,560,820,280` at 200M, `231 * costU ≤ 47,863,280,820,280` at 380M)
     yielding `mainUncached200 = 111,614,505,033` (`8×` Yukon passes, `9×` fails) and
     `mainUncached380 = 208,876,066,898` (`4×` Yukon passes, `5×` fails).
2. **`JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster` &
   `SelfContainedJumpdestDualLPOneHundredTwelveCampaignMaster`**:
   - Strict improvement from `110×`/`77×` (`8,145,414,250`, `11,669,833,258`) and `8×`/`4×`
     (`112,163,577,490`, `209,425,139,355`) to `112×`/`77×` (`8,014,558,459`, `11,548,778,048`)
     and `8×`/`4×` (`111,614,505,033`, `208,876,066,898`),
   - Full self-contained compiler contracts (`StackAlloc` identity, `NoGcCall`, `StackRemove` zero extra body clock),
   - 114-budget portfolio (`OneHundredFourteenShape`, max `900,715,000,000`, margin `4,925,474` below Yukon)
     extending `OneHundredTwelveShape`, `OneHundredTenShape`, `OneHundredEightShape`, `OneHundredSixShape`,
     and `OneHundredFourShape`,
   - Conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)` integration across all 114 budgets.
-/

namespace InitECandidate.Solver.SelfContainedWitnessEmptyItemPushOneHundredFourteenCampaignMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster (
  inputBytes
  fixed200
  fixed380
  keccakEmpty
  push31
  costC
  costU
  mainCached200
  mainCached380
  mainUncached200
  mainUncached380
  leaf_counts
  cached200
  cached380
  uncached200
  uncached380
  cached_slopes
  uncached_slopes
  no_135
)
open _root_.InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster (
  callTicks
  call_val
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
open _root_.InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster (
  oneHundredFourteenExplicitBudgets
  OneHundredFourteenShape
  one_hundred_fourteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight
  one_hundred_fourteen_budgets_under_yukon_non_vacuous_and_tight
  one_hundred_fourteen_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredTwelveBudgetMaster (
  oneHundredTwelveExplicitBudgets
  OneHundredTwelveShape
  one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
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
open _root_.InitECandidate.Solver.SelfContainedJumpdestDualLPOneHundredTwelveCampaignMaster (
  compiler_stack_alloc_no_gc_and_jumpdest_dual_lp_non_vacuous_and_tight
  stack_remove_base_and_space_clock_and_dual_lp_slopes_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestDualCampaignMaster (
  cachedMain200
  cachedMain380
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

abbrev portfolio : List Nat := oneHundredFourteenExplicitBudgets

/-- 1. Exact witness empty-item and `PUSH31` leaf counts (`keccakEmpty = 35`, `push31 = 54 = 18 * 3`)
paired with the `sstore`/`sload`/`call` static base ticks (`110`, `82`, `349`, `callTicks = 67,884`)
and the `135×` ceiling exclusion (`yukon / 135 = 6,671,999,447`, `yukon < 135 * mainCached200`). -/
theorem witness_empty_item_push_leaf_counts_and_no_135_non_vacuous_and_tight :
    (keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3) ∧
    (sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349 ∧
      callTicks = 67884 ∧ maxCode = 65536 ∧ callGas = 126) ∧
    (yukon / 135 = 6671999447 ∧ yukon < 135 * mainCached200 ∧
      135 * mainCached200 - yukon = 181245466491) := by
  exact ⟨leaf_counts, by decide, no_135.1, no_135.2, by decide⟩

/-- 2. Cached full LP bounds (`cached200`, `cached380`) with exact empty-entry (`43`), short-entry
(`79`), leaf/ext (`127`), and branch (`405`) witness weights, yielding `mainCached200 = 8,014,558,459`
(`112×` Yukon passes, `113×` fails) and `mainCached380 = 11,548,778,048` (`77×` Yukon passes,
`78×` fails). -/
theorem cached200_cached380_and_one_hundred_twelve_x_seventy_seven_x_slopes_non_vacuous_and_tight
    (A K B E n2 n17 md ms P : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (2400 * A + 2100 * K + P ≤ 200000000 →
      33 * costC A K B E n2 n17 md ms P ≤ 214138410040 ∧
      fixed200 + inputBytes + costC A K B E n2 n17 md ms P ≤ mainCached200) ∧
    (2400 * A + 2100 * K + P ≤ 380000000 →
      11803 * costC A K B E n2 n17 md ms P ≤ 114947567578464 ∧
      fixed380 + inputBytes + costC A K B E n2 n17 md ms P ≤ mainCached380) ∧
    (mainCached200 = 8014558459 ∧ 112 * mainCached200 < yukon ∧ yukon < 113 * mainCached200 ∧
      yukon - 112 * mainCached200 = 3089378066) ∧
    (mainCached380 = 11548778048 ∧ 77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380 ∧
      yukon - 77 * mainCached380 = 11464015778) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro hg
    have hc := cached200 A K B E n2 n17 md ms P hg h1 h2 hb he hw
    refine ⟨hc, ?_⟩
    unfold mainCached200 fixed200 inputBytes at *
    omega
  · intro hg
    have hc := cached380 A K B E n2 n17 md ms P hg h1 h2 hb he hw
    refine ⟨hc, ?_⟩
    unfold mainCached380 fixed380 inputBytes at *
    omega

/-- 3. Uncached full LP bounds (`uncached200`, `uncached380`) closing the `(B, E, n2, n17)` reserve,
yielding `mainUncached200 = 111,614,505,033` (`8×` Yukon passes, `9×` fails) and
`mainUncached380 = 208,876,066,898` (`4×` Yukon passes, `5×` fails). -/
theorem uncached200_uncached380_and_eight_x_four_x_slopes_non_vacuous_and_tight
    (A K B E n2 n17 md ms P C T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    (2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 200000000 →
      231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 ∧
      fixed200 + costU A K B E n2 n17 md ms P C T ≤ mainUncached200) ∧
    (2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 380000000 →
      231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 ∧
      fixed380 + costU A K B E n2 n17 md ms P C T ≤ mainUncached380) ∧
    (mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      yukon - 8 * mainUncached200 = 7803885210) ∧
    (mainUncached380 = 208876066898 ∧ 4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380 ∧
      yukon - 4 * mainUncached380 = 65215657882) := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro hg
    have hu := uncached200 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw
    refine ⟨hu, ?_⟩
    unfold mainUncached200 fixed200 at *
    omega
  · intro hg
    have hu := uncached380 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw
    refine ⟨hu, ?_⟩
    unfold mainUncached380 fixed380 at *
    omega

/-- 4. Strict reduction from the `110×`/`77×` cached LP (`8,145,414,250` / `11,669,833,258`) and
previous `8×`/`4×` uncached LP (`112,163,577,490` / `209,425,139,355`) to the exact empty-item
witness LP (`8,014,558,459` / `11,548,778,048` cached, `111,614,505,033` / `208,876,066,898` uncached). -/
theorem witness_empty_item_lp_strict_reduction_over_previous_dual_lp_non_vacuous_and_tight :
    (GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 = 8145414250 ∧
      mainCached200 = 8014558459 ∧
      mainCached200 < GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 - mainCached200 = 130855791) ∧
    (GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 = 11669833258 ∧
      mainCached380 = 11548778048 ∧
      mainCached380 < GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 - mainCached380 = 121055210) ∧
    (GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached200 = 112163577490 ∧
      mainUncached200 = 111614505033 ∧
      mainUncached200 < GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached200 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached200 - mainUncached200 = 549072457) ∧
    (GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached380 = 209425139355 ∧
      mainUncached380 = 208876066898 ∧
      mainUncached380 < GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached380 ∧
      GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached380 - mainUncached380 = 549072457) := by
  decide

/-- 5. Multi-stage slope progression from `78×` (`11,546,768,760`), `106×` (`8,432,330,917`),
`108×` (`8,298,113,205`), and `110×` (`8,145,414,250`) to `112×` (`8,014,558,459`) at 200M, and
from `52×` (`17,251,948,659`) and `75×` (`11,992,988,211`) to `77×` (`11,548,778,048`) at 380M. -/
theorem campaign_slope_progression_seventy_eight_to_one_hundred_twelve_x_non_vacuous_and_tight :
    (112 * mainCached200 < yukon ∧ yukon < 113 * mainCached200 ∧
      110 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 < yukon ∧
      yukon < 111 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 ∧
      108 * 8298113205 < yukon ∧ yukon < 109 * 8298113205 ∧
      106 * cachedMain200 < yukon ∧ yukon < 107 * cachedMain200 ∧
      78 * 11546768760 < yukon ∧ yukon < 79 * 11546768760 ∧
      8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200) ∧
    (77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380 ∧
      77 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 < yukon ∧
      yukon < 78 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 ∧
      75 * 11858770499 < yukon ∧ yukon < 76 * 11858770499 ∧
      75 * cachedMain380 < yukon ∧ yukon < 76 * cachedMain380 ∧
      52 * 17251948659 < yukon ∧ yukon < 53 * 17251948659 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) := by
  decide

/-- 6. Full self-contained `StackAlloc` identity, unconditional `NoGcCall`, and `StackRemove`
zero-extra-body-clock contract paired with `leaf_counts` and the `112×`/`77×` cached and `8×`/`4×`
uncached LP bounds. -/
theorem compiler_stack_alloc_no_gc_and_witness_empty_item_push_lp_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (n m : Nat) (w : WordLocW width) :
    (((((∀ y ∈ rawCallSections arch prog wc ac perf,
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
    (110 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached200 < yukon ∧
      77 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainCached380 < yukon ∧
      8 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached200 < yukon ∧
      4 * GuestExactSstoreCallLPAndJumpdestDualBoundMaster.mainUncached380 < yukon)) ∧
    (keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3 ∧
      112 * mainCached200 < yukon ∧ 77 * mainCached380 < yukon ∧
      8 * mainUncached200 < yukon ∧ 4 * mainUncached380 < yukon) :=
  ⟨compiler_stack_alloc_no_gc_and_jumpdest_dual_lp_non_vacuous_and_tight
     (C := C) (F := F) arch prog wc ac perf dc info n m w,
   by decide⟩

/-- 7. Self-contained `StackRemove` base-case and stack-space simulation contracts paired with the
`112×`/`77×` cached and `8×`/`4×` uncached LP slopes. -/
theorem stack_remove_base_and_space_clock_and_one_hundred_twelve_x_slopes_non_vacuous_and_tight
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
    (112 * mainCached200 < yukon ∧ yukon < 113 * mainCached200 ∧
      77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380 ∧
      8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) :=
  ⟨(stack_remove_base_and_space_clock_and_dual_lp_slopes_non_vacuous_and_tight source result
     postSource target register count pointer bounds jump).1,
   by decide⟩

/-- 8. Six-tier budget portfolio hierarchy: `OneHundredFourteenShape` (114 budgets, max `900,715,000,000`,
margin `4,925,474`), `OneHundredTwelveShape` (112 budgets, max `900,700,000,000`, margin `19,925,474`),
`OneHundredTenShape` (110 budgets), `OneHundredEightShape` (108 budgets), `OneHundredSixShape`
(106 budgets), and `OneHundredFourShape` (104 budgets), all strictly increasing and `< yukon`. -/
theorem one_hundred_fourteen_to_one_hundred_four_budget_hierarchy_non_vacuous_and_tight :
    OneHundredFourteenShape ∧
    OneHundredTwelveShape ∧
    OneHundredTenShape ∧
    OneHundredEightShape ∧
    OneHundredSixShape ∧
    OneHundredFourShape ∧
    oneHundredFourteenExplicitBudgets.length = 114 ∧
    oneHundredFourteenExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredFourteenExplicitBudgets, 1212035192 ≤ K ∧ K < 900719925474) ∧
    oneHundredFourteenExplicitBudgets.drop 112 = [900710000000, 900715000000] ∧
    oneHundredFourteenExplicitBudgets.getLast? = some 900715000000 ∧
    yukon - 900715000000 = 4925474 ∧
    yukon - 900700000000 = 19925474 :=
  have h114 := one_hundred_fourteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h112 := one_hundred_twelve_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h110 := one_hundred_ten_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h108 := one_hundred_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h106 := one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h104 := one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  ⟨h114,
   h112,
   h110,
   h108,
   h106,
   h104,
   h114.1,
   h114.2.1,
   h114.2.2.1,
   h114.2.2.2.2.1,
   h114.2.2.2.2.2.1,
   by decide,
   by decide⟩

/-- 9. Conditional finite certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)`
across all 114 budgets, plus explicit certificates at the new endpoints `900,710,000,000` and
`900,715,000,000` and at the witness-empty-item dual LP budgets `mainCached200`, `mainCached380`,
`mainUncached200`, and `mainUncached380`. -/
theorem one_hundred_fourteen_budget_and_witness_lp_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredFourteenShape ∧
    (∀ K ∈ oneHundredFourteenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK mainCached200) (.finite mainCached200) ∧
    InitE.Certificate (baselineWithFiniteK mainCached380) (.finite mainCached380) ∧
    InitE.Certificate (baselineWithFiniteK mainUncached200) (.finite mainUncached200) ∧
    InitE.Certificate (baselineWithFiniteK mainUncached380) (.finite mainUncached380) ∧
    InitE.Certificate (baselineWithFiniteK 900710000000) (.finite 900710000000) ∧
    InitE.Certificate (baselineWithFiniteK 900715000000) (.finite 900715000000) := by
  have hcert := one_hundred_fourteen_budget_certificates_non_vacuous_and_tight cert
  refine ⟨hcert.1, hcert.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainCached200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainCached380 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainUncached200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ mainUncached380 (by decide) cert
  · exact hcert.2 900710000000 (by decide)
  · exact hcert.2 900715000000 (by decide)

/-- 10. Grand campaign master synthesis: `leaf_counts` (`keccakEmpty = 35`, `push31 = 54 = 18 * 3`),
`cached200`, `cached380`, `uncached200`, `uncached380`, `cached_slopes` (`112×` at 200M, `77×` at
380M), `uncached_slopes` (`8×` at 200M, `4×` at 380M), 114-budget portfolio (`OneHundredFourteenShape`,
max `900,715,000,000`, margin `4,925,474`), and conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)`
across all 114 budgets. -/
theorem grand_witness_empty_item_push_one_hundred_fourteen_campaign_master_non_vacuous_and_tight
    (A K B E n2 n17 md ms P C T : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes)
    (cert : CertificateAt 1212035192) :
    (keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3) ∧
    (2400 * A + 2100 * K + P ≤ 200000000 →
      33 * costC A K B E n2 n17 md ms P ≤ 214138410040) ∧
    (2400 * A + 2100 * K + P ≤ 380000000 →
      11803 * costC A K B E n2 n17 md ms P ≤ 114947567578464) ∧
    (2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 200000000 →
      231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280) ∧
    (2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 380000000 →
      231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280) ∧
    (mainCached200 = 8014558459 ∧ 112 * mainCached200 < yukon ∧ yukon < 113 * mainCached200 ∧
      mainCached380 = 11548778048 ∧ 77 * mainCached380 < yukon ∧ yukon < 78 * mainCached380) ∧
    (mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧ yukon < 9 * mainUncached200 ∧
      mainUncached380 = 208876066898 ∧ 4 * mainUncached380 < yukon ∧ yukon < 5 * mainUncached380) ∧
    OneHundredFourteenShape ∧
    yukon - 900715000000 = 4925474 ∧
    (∀ K_b ∈ oneHundredFourteenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K_b) (.finite K_b)) := by
  have hcert := one_hundred_fourteen_budget_certificates_non_vacuous_and_tight cert
  refine ⟨leaf_counts, ?_, ?_, ?_, ?_, cached_slopes, uncached_slopes, hcert.1, by decide, hcert.2⟩
  · intro hg
    exact cached200 A K B E n2 n17 md ms P hg h1 h2 hb he hw
  · intro hg
    exact cached380 A K B E n2 n17 md ms P hg h1 h2 hb he hw
  · intro hg
    exact uncached200 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw
  · intro hg
    exact uncached380 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

#print axioms witness_empty_item_push_leaf_counts_and_no_135_non_vacuous_and_tight
#print axioms cached200_cached380_and_one_hundred_twelve_x_seventy_seven_x_slopes_non_vacuous_and_tight
#print axioms uncached200_uncached380_and_eight_x_four_x_slopes_non_vacuous_and_tight
#print axioms witness_empty_item_lp_strict_reduction_over_previous_dual_lp_non_vacuous_and_tight
#print axioms campaign_slope_progression_seventy_eight_to_one_hundred_twelve_x_non_vacuous_and_tight
#print axioms compiler_stack_alloc_no_gc_and_witness_empty_item_push_lp_non_vacuous_and_tight
#print axioms stack_remove_base_and_space_clock_and_one_hundred_twelve_x_slopes_non_vacuous_and_tight
#print axioms one_hundred_fourteen_to_one_hundred_four_budget_hierarchy_non_vacuous_and_tight
#print axioms one_hundred_fourteen_budget_and_witness_lp_certificates_non_vacuous_and_tight
#print axioms grand_witness_empty_item_push_one_hundred_fourteen_campaign_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedWitnessEmptyItemPushOneHundredFourteenCampaignMaster
