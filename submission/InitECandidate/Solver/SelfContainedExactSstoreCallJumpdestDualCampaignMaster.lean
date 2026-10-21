import InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster
import InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestDualCampaignMaster` (`W5_283`)

Self-contained dual campaign synthesis (`0 sorryAx`, `0` imports from `InitECandidate.Proofs.Bounded*`)
uniting:
1. **`GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster`**:
   - Exact `PanSem` straight-line static call-graph counts (`sstoreBaseTicks = 110`,
     `sloadBaseTicks = 82`, `accountAccessBaseTicks = 349`, `charges_ok`),
   - Per-call `compute_jumpdests` scan ratio (`callGas = 126`, `maxCode = 65536`,
     `18 * callGas < maxCode`, `28 * (18 * callGas) < maxCode`),
   - Uncached `compute_jumpdests` lower bounds:
     - at 200M gas: `jumpdestTicks 200_000_000 = 104_025_358_336` (`8×` Yukon passes, `9×` fails,
       exceeding the `108×` row `8_298_113_205` by `> 12×`),
     - at 380M gas: `jumpdestTicks 380_000_000 = 197_648_252_928` (`4×` Yukon passes, `5×` fails),
   - Cached `compute_jumpdests` (scan each distinct code at most once, `≤ 134_217_712` bytes total):
     - at 200M gas: `8_298_113_205 + 134_217_712 = 8_432_330_917` (`106×` Yukon passes, `107×` fails),
     - at 380M gas: `11_858_770_499 + 134_217_712 = 11_992_988_211` (`75×` Yukon passes, `76×` fails),
   - Transaction intrinsic-gas count (`200_000_000 / 12_000 = 16_666` vs `200_000_000 / 21_000 = 9_523`).
2. **`GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster`**:
   - Global gas-coupled LP bounds (`3 * cost ≤ 20_720_445_560` at 200M,
     `65 * cost ≤ 661_898_475_728` at 380M),
   - Full self-contained compiler contracts (`pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_two_bridge`,
     `stack_remove_base_and_space_clock_one_hundred_two_bridge`),
   - 106-budget portfolio (`OneHundredSixShape`) and conditional `InitE.Certificate` integration.
-/

namespace InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestDualCampaignMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster (
  sstoreBaseTicks
  sloadBaseTicks
  accountAccessBaseTicks
  maxCode
  callGas
  calls
  jumpdestTicks
  charges_ok
  scan_ratio
  attack200
  attack380
  previous_broken
  cached
  tx_count
)
open _root_.InitECandidate.Solver.GuestGlobalGasCoupledEvmAndSubNineBillionMaster (
  inputBytes
  cost
  fixed200
  fixed380
  main200
  main380
)
open _root_.InitECandidate.Solver.GlobalGasCoupledOneHundredEightXAndOneHundredSixBudgetMaster (
  oneHundredFourExplicitFiniteKBugdetTable
  oneHundredSixExplicitFiniteKBugdetTable
  portfolio
  OneHundredSixShape
  fixed_vals_non_vacuous_and_tight
  joint200_non_vacuous_and_tight
  joint380_non_vacuous_and_tight
  main200_slope_non_vacuous_and_tight
  main380_slope_non_vacuous_and_tight
  margins_non_vacuous_and_tight
  all_push_and_sensitivity_non_vacuous_and_tight
  improvement200_non_vacuous_and_tight
  improvement380_non_vacuous_and_tight
  one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  one_hundred_six_budget_last_margin_non_vacuous_and_tight
  one_hundred_six_budget_certificates_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredFourBudgetMaster (
  OneHundredFourShape
  one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
)
open _root_.InitECandidate.Solver.EvmStepDispatchSeventyEightXAndOneHundredTwoBudgetCampaignBridge (
  pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_two_bridge_non_vacuous_and_tight
  stack_remove_base_and_space_clock_one_hundred_two_bridge_non_vacuous_and_tight
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

/-- Cached 200M total (`main200 + inputBytes = 8,432,330,917`). -/
def cachedMain200 : Nat := main200 + inputBytes

/-- Cached 380M total (`main380 + inputBytes = 11,992,988,211`). -/
def cachedMain380 : Nat := main380 + inputBytes

/-- 1. Exact `PanSem` static call-graph base tick counts (`sstoreBaseTicks = 110`,
`sloadBaseTicks = 82`, `accountAccessBaseTicks = 349`), per-key/per-account charge validation,
and transaction intrinsic-gas bound (`16,666` at `12,000` gas vs `9,523` at `21,000` gas). -/
theorem exact_sstore_sload_call_base_ticks_and_tx_count_non_vacuous_and_tight :
    (sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349 ∧
      maxCode = 65536 ∧ callGas = 126) ∧
    (sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
      sloadBaseTicks + 7 * 28 ≤ 18 * 100) ∧
    (2000 - sstoreBaseTicks = 1890 ∧ 10000 - accountAccessBaseTicks = 9651 ∧
      18 * 100 - (sloadBaseTicks + 7 * 28) = 1522) ∧
    (200000000 / 12000 = 16666 ∧ 200000000 / 21000 = 9523 ∧
      16666 - 9523 = 7143) := by
  refine ⟨by decide, charges_ok, by decide, ?_⟩
  exact ⟨tx_count.1, tx_count.2, by decide⟩

/-- 2. Per-call `compute_jumpdests` scan ratio (`> 28×` above `18 * callGas`) and uncached
`compute_jumpdests` lower bounds at 200M (`104,025,358,336`, `8×` Yukon passes, `9×` fails) and
380M (`197,648,252,928`, `4×` Yukon passes, `5×` fails), breaking `8,298,113,205` by `> 12×`. -/
theorem uncached_jumpdest_scan_ratio_and_eight_x_four_x_bounds_non_vacuous_and_tight :
    (18 * callGas = 2268 ∧ 18 * callGas < maxCode ∧ 28 * (18 * callGas) < maxCode ∧
      maxCode < 29 * (18 * callGas)) ∧
    (calls 200000000 = 1587301 ∧ jumpdestTicks 200000000 = 104025358336 ∧
      8 * jumpdestTicks 200000000 < yukon ∧ yukon < 9 * jumpdestTicks 200000000 ∧
      yukon - 8 * jumpdestTicks 200000000 = 68517058786) ∧
    (calls 380000000 = 3015873 ∧ jumpdestTicks 380000000 = 197648252928 ∧
      4 * jumpdestTicks 380000000 < yukon ∧ yukon < 5 * jumpdestTicks 380000000 ∧
      yukon - 4 * jumpdestTicks 380000000 = 110126913762) ∧
    (12 * main200 < jumpdestTicks 200000000 ∧ jumpdestTicks 200000000 < 13 * main200) := by
  decide

/-- 3. Cached `compute_jumpdests` bound (scanning each distinct code at most once, adding at most
`inputBytes = 134,217,712` ticks): `cachedMain200 = 8,432,330,917` (`106×` Yukon passes, `107×`
fails) and `cachedMain380 = 11,992,988,211` (`75×` Yukon passes, `76×` fails). -/
theorem cached_jumpdest_one_hundred_six_x_and_seventy_five_x_bounds_non_vacuous_and_tight :
    (cachedMain200 = 8432330917 ∧ 8298113205 + 134217712 = 8432330917 ∧
      106 * cachedMain200 < yukon ∧ yukon < 107 * cachedMain200 ∧
      yukon - 106 * cachedMain200 = 6892848272) ∧
    (cachedMain380 = 11992988211 ∧ 11858770499 + 134217712 = 11992988211 ∧
      75 * cachedMain380 < yukon ∧ yukon < 76 * cachedMain380 ∧
      yukon - 75 * cachedMain380 = 1245809649) ∧
    (jumpdestTicks 200000000 - cachedMain200 = 95593027419 ∧
      jumpdestTicks 380000000 - cachedMain380 = 185655264717) := by
  decide

/-- 4. Dual comparison of uncached (`8×` at 200M, `4×` at 380M), cached (`106×` at 200M, `75×` at
380M), and straight-line global-gas (`108×` at 200M, `75×` at 380M) totals. -/
theorem dual_uncached_vs_cached_vs_straight_line_comparison_non_vacuous_and_tight :
    (main200 = 8298113205 ∧ cachedMain200 = 8432330917 ∧
      jumpdestTicks 200000000 = 104025358336 ∧
      main200 < cachedMain200 ∧ cachedMain200 < jumpdestTicks 200000000 ∧
      108 * main200 < yukon ∧ yukon < 109 * main200 ∧
      106 * cachedMain200 < yukon ∧ yukon < 107 * cachedMain200 ∧
      8 * jumpdestTicks 200000000 < yukon ∧ yukon < 9 * jumpdestTicks 200000000) ∧
    (main380 = 11858770499 ∧ cachedMain380 = 11992988211 ∧
      jumpdestTicks 380000000 = 197648252928 ∧
      main380 < cachedMain380 ∧ cachedMain380 < jumpdestTicks 380000000 ∧
      75 * main380 < yukon ∧ yukon < 76 * main380 ∧
      75 * cachedMain380 < yukon ∧ yukon < 76 * cachedMain380 ∧
      4 * jumpdestTicks 380000000 < yukon ∧ yukon < 5 * jumpdestTicks 380000000) := by
  decide

/-- 5. Global gas-coupled LP bounds at 200M and 380M paired with the cached `compute_jumpdests`
additive bound (`3 * (cost + inputBytes) ≤ 20,720,445,560 + 3 * inputBytes`). -/
theorem global_gas_lp_and_cached_jumpdest_joint_bounds_non_vacuous_and_tight
    (A K B E n2 n17 m P : Nat)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    (fixed200 = 1391298018 ∧ fixed380 = 1675717026) ∧
    (24 * A + 21 * K + P ≤ 2000000 →
      3 * cost A K B E n2 n17 m P ≤ 20720445560 ∧
      3 * (cost A K B E n2 n17 m P + inputBytes) ≤ 21123098696) ∧
    (24 * A + 21 * K + P ≤ 3800000 →
      65 * cost A K B E n2 n17 m P ≤ 661898475728 ∧
      65 * (cost A K B E n2 n17 m P + inputBytes) ≤ 670622627008) ∧
    (3 * cost 0 0 0 0 0 0 (inputBytes / 4) 2000000 ≤ 20720445560 ∧
      98 * 9131446538 < yukon ∧ yukon < 99 * 9131446538) := by
  refine ⟨fixed_vals_non_vacuous_and_tight, ?_, ?_, all_push_and_sensitivity_non_vacuous_and_tight⟩
  · intro hg
    have hj := joint200_non_vacuous_and_tight A K B E n2 n17 m P hg h1 h2 hb he hw
    refine ⟨hj, ?_⟩
    unfold inputBytes at *
    omega
  · intro hg
    have hj := joint380_non_vacuous_and_tight A K B E n2 n17 m P hg h1 h2 hb he hw
    refine ⟨hj, ?_⟩
    unfold inputBytes at *
    omega

/-- 6. Progression from `78×` (`11,546,768,760`) to `106×` cached (`8,432,330,917`) and `108×`
straight-line (`8,298,113,205`) at 200M, and from `52×` (`17,251,948,659`) to `75×` cached
(`11,992,988,211`) and `75×` straight-line (`11,858,770,499`) at 380M. -/
theorem cached_and_straight_line_improvement_over_seventy_eight_x_non_vacuous_and_tight :
    (GuestEvmStepDispatchAndNinetyXMaster.main200 = 11546768760 ∧
      cachedMain200 < GuestEvmStepDispatchAndNinetyXMaster.main200 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main200 - cachedMain200 = 3114437843 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main200 - main200 = 3248655555) ∧
    (GuestEvmStepDispatchAndNinetyXMaster.main380 = 17251948659 ∧
      cachedMain380 < GuestEvmStepDispatchAndNinetyXMaster.main380 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main380 - cachedMain380 = 5258960448 ∧
      GuestEvmStepDispatchAndNinetyXMaster.main380 - main380 = 5393178160) := by
  decide

/-- 7. Full self-contained `StackAlloc` identity, unconditional `NoGcCall`, and `StackRemove`
zero-extra-body-clock contract paired with the exact `sstore`/`sload`/`call` tick counts and
dual `compute_jumpdests` bounds. -/
theorem compiler_stack_alloc_no_gc_and_exact_sstore_jumpdest_dual_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (n m : Nat) (w : WordLocW width) :
    (((∀ y ∈ rawCallSections arch prog wc ac perf,
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
      106 * cachedMain200 < yukon ∧ 75 * cachedMain380 < yukon) :=
  ⟨pancake_stackAllocIdentity_noGc_zeroExtraClock_one_hundred_two_bridge_non_vacuous_and_tight
     (C := C) (F := F) arch prog wc ac perf dc info n m w,
   by decide,
   by decide⟩

/-- 8. Self-contained `StackRemove` base-case and stack-space simulation contracts paired with the
dual uncached/cached `compute_jumpdests` bounds. -/
theorem stack_remove_base_and_space_clock_and_jumpdest_dual_non_vacuous_and_tight
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
    (8 * jumpdestTicks 200000000 < yukon ∧ yukon < 9 * jumpdestTicks 200000000 ∧
      4 * jumpdestTicks 380000000 < yukon ∧ yukon < 5 * jumpdestTicks 380000000 ∧
      106 * cachedMain200 < yukon ∧ yukon < 107 * cachedMain200 ∧
      75 * cachedMain380 < yukon ∧ yukon < 76 * cachedMain380) :=
  ⟨stack_remove_base_and_space_clock_one_hundred_two_bridge_non_vacuous_and_tight source result
     postSource target register count pointer bounds jump,
   by decide⟩

/-- 9. Strictly increasing 106-budget portfolio (`OneHundredSixShape`) extending the 104-budget
(`OneHundredFourShape`) table, with all 106 budgets `< 900_719_925_474` and endpoint margin
`6,219,925,474`. -/
theorem one_hundred_six_and_one_hundred_four_budget_hierarchy_non_vacuous_and_tight :
    OneHundredSixShape ∧
    OneHundredFourShape ∧
    oneHundredSixExplicitFiniteKBugdetTable.length = 106 ∧
    oneHundredSixExplicitFiniteKBugdetTable.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable, 1212035192 ≤ K ∧ K < 900719925474) ∧
    oneHundredSixExplicitFiniteKBugdetTable.drop 104 = [893500000000, 894500000000] ∧
    oneHundredSixExplicitFiniteKBugdetTable.getLast? = some 894500000000 ∧
    yukon - 894500000000 = 6219925474 :=
  have h106 := one_hundred_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  have h104 := one_hundred_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
  ⟨h106,
   h104,
   h106.1,
   h106.2.1,
   h106.2.2.1,
   h106.2.2.2.2.1,
   h106.2.2.2.2.2.1,
   by decide⟩

/-- 10. Grand dual synthesis: exact `sstore`/`sload`/`call` counts (`110`, `82`, `349`), uncached
`compute_jumpdests` (`8×` at 200M, `4×` at 380M), cached `compute_jumpdests` (`106×` at 200M,
`75×` at 380M), and conditional `InitE.Certificate (baselineWithFiniteK K) (.finite K)` across all
106 portfolio budgets plus the uncached/cached target budgets. -/
theorem grand_exact_sstore_call_jumpdest_dual_and_finite_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (sstoreBaseTicks = 110 ∧ sloadBaseTicks = 82 ∧ accountAccessBaseTicks = 349 ∧
      sstoreBaseTicks ≤ 2000 ∧ accountAccessBaseTicks ≤ 10000 ∧
      sloadBaseTicks + 7 * 28 ≤ 18 * 100) ∧
    (jumpdestTicks 200000000 = 104025358336 ∧ 8 * jumpdestTicks 200000000 < yukon ∧
      yukon < 9 * jumpdestTicks 200000000 ∧
      jumpdestTicks 380000000 = 197648252928 ∧ 4 * jumpdestTicks 380000000 < yukon ∧
      yukon < 5 * jumpdestTicks 380000000) ∧
    (cachedMain200 = 8432330917 ∧ 106 * cachedMain200 < yukon ∧ yukon < 107 * cachedMain200 ∧
      cachedMain380 = 11992988211 ∧ 75 * cachedMain380 < yukon ∧ yukon < 76 * cachedMain380) ∧
    OneHundredSixShape ∧
    (∀ K ∈ oneHundredSixExplicitFiniteKBugdetTable,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    InitE.Certificate (baselineWithFiniteK cachedMain200) (.finite cachedMain200) ∧
    InitE.Certificate (baselineWithFiniteK (jumpdestTicks 200000000))
      (.finite (jumpdestTicks 200000000)) ∧
    InitE.Certificate (baselineWithFiniteK 893500000000) (.finite 893500000000) ∧
    InitE.Certificate (baselineWithFiniteK 894500000000) (.finite 894500000000) := by
  have hcert := one_hundred_six_budget_certificates_non_vacuous_and_tight cert
  refine ⟨by decide, by decide, by decide, hcert.1, hcert.2, ?_, ?_, ?_, ?_⟩
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ cachedMain200 (by decide) cert
  · exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
      _ (jumpdestTicks 200000000) (by decide) cert
  · exact hcert.2 893500000000 (by decide)
  · exact hcert.2 894500000000 (by decide)

#print axioms exact_sstore_sload_call_base_ticks_and_tx_count_non_vacuous_and_tight
#print axioms uncached_jumpdest_scan_ratio_and_eight_x_four_x_bounds_non_vacuous_and_tight
#print axioms cached_jumpdest_one_hundred_six_x_and_seventy_five_x_bounds_non_vacuous_and_tight
#print axioms dual_uncached_vs_cached_vs_straight_line_comparison_non_vacuous_and_tight
#print axioms global_gas_lp_and_cached_jumpdest_joint_bounds_non_vacuous_and_tight
#print axioms cached_and_straight_line_improvement_over_seventy_eight_x_non_vacuous_and_tight
#print axioms compiler_stack_alloc_no_gc_and_exact_sstore_jumpdest_dual_non_vacuous_and_tight
#print axioms stack_remove_base_and_space_clock_and_jumpdest_dual_non_vacuous_and_tight
#print axioms one_hundred_six_and_one_hundred_four_budget_hierarchy_non_vacuous_and_tight
#print axioms grand_exact_sstore_call_jumpdest_dual_and_finite_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedExactSstoreCallJumpdestDualCampaignMaster
