import InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster
import InitECandidate.Solver.CoupledGasStackRemoveZeroClockCampaignBridge
import InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroCampaignBridge`

Wave 5 bridge (`W5_189`) unifying:
* `GuestEndToEndStartToHaltAndCoupledMptMaster` (`11/11` tight): exact `619,060,000`-tick saving on
  `mpt_set` by coupling MPT state-root writes to the shared `200M` gas budget (`224,366,249,693`
  without memoization, `195,035,480,749` with DAG memoization), plus `1×` / `4×` Yukon residuals;
* `CoupledGasStackRemoveZeroClockCampaignBridge` (`10/10` tight): shared-budget `ts+64` absorption
  for `L ≤ 5,000` and zero-clock simulation guarantees (`clock = 0`) for `StackRemove` base cases;
* `EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster` (`12/12` tight): coupled-MPT `1×` /
  `4×` Yukon thresholds (`38,817 / 40,284` and `5,040 / 6,507`), the strictly increasing 68-budget
  portfolio `< 900,719,925,474`, and conditional finite certificates
  `InitE.Certificate (baselineWithFiniteK K) (.finite K)`.

No `InitECandidate.Proofs.Bounded*` imports.
-/

namespace InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroCampaignBridge

open InitECandidate.Solver.GuestEndToEndStartToHaltAndCoupledMptMaster
open InitECandidate.Solver.CoupledGasStackRemoveZeroClockCampaignBridge
open InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (coupled excess)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- 1. Shared `200M` gas budget coupling for `mpt_set`: at most `95,238` written keys (`21` units
each), bounding coupled state-root writes to `12,380,940,000` ticks and saving exactly
`619,060,000` ticks against `13,000,000,000`. -/
theorem coupled_mpt_write_saving_and_dirty_keys_non_vacuous_and_tight :
    (∀ k : Nat, 21 * k ≤ 2000000 → k ≤ 95238 ∧ 130000 * k ≤ 12380940000) ∧
    (21 * 95238 ≤ 2000000 ∧ 2000000 < 21 * 95239) ∧
    130000 * 95238 = 12380940000 ∧
    13000000000 - 130000 * 95238 = 619060000 :=
  mpt_write_saving_non_vacuous_and_tight

/-- 2. Coupled-MPT full-block totals (`224,366,249,693` heap and `195,035,480,749` DAG-memoized),
fourfold Yukon fit, and exact `1×` / `4×` Yukon residual budgets. -/
theorem coupled_mpt_block_totals_and_yukon_residuals_non_vacuous_and_tight :
    (block_total_coupled_mpt = 224366249693 ∧
      block_total_memo_coupled_mpt = 195035480749 ∧
      4 * block_total_memo_coupled_mpt = 780141922996 ∧
      4 * block_total_memo_coupled_mpt < yukon ∧
      4 * block_total_coupled_mpt < yukon ∧
      yukon ≤ 5 * block_total_memo_coupled_mpt ∧
      yukon ≤ 5 * block_total_coupled_mpt) ∧
    yukon - 224366249693 = 676353675781 ∧
    (yukon / 4 - 224366249693 = 813731675 ∧
      yukon / 4 - 195035480749 = 30144500619) :=
  ⟨coupled_mpt_totals_non_vacuous_and_tight, residual_1x, residual_4x⟩

/-- 3. Exact `1×` Yukon collision-probe thresholds with coupled MPT writes: `L ≤ 38,817` (heap)
and `L ≤ 40,284` (DAG-memoized). -/
theorem coupled_mpt_one_yukon_thresholds_non_vacuous_and_tight :
    ((∀ L : Nat, 1 * coupled block_total_coupled_mpt L < yukon ↔ L ≤ 38817) ∧
      1 * coupled block_total_coupled_mpt 38817 < yukon ∧
      yukon ≤ 1 * coupled block_total_coupled_mpt 38818) ∧
    ((∀ L : Nat, 1 * coupled block_total_memo_coupled_mpt L < yukon ↔ L ≤ 40284) ∧
      1 * coupled block_total_memo_coupled_mpt 40284 < yukon ∧
      yukon ≤ 1 * coupled block_total_memo_coupled_mpt 40285) :=
  ⟨one_heap_non_vacuous_and_tight, one_memo_non_vacuous_and_tight⟩

/-- 4. Exact `4×` Yukon collision-probe thresholds with coupled MPT writes: `L ≤ 5,040` (heap)
and `L ≤ 6,507` (DAG-memoized). -/
theorem coupled_mpt_four_yukon_thresholds_non_vacuous_and_tight :
    ((∀ L : Nat, 4 * coupled block_total_coupled_mpt L < yukon ↔ L ≤ 5040) ∧
      4 * coupled block_total_coupled_mpt 5040 < yukon ∧
      yukon ≤ 4 * coupled block_total_coupled_mpt 5041) ∧
    ((∀ L : Nat, 4 * coupled block_total_memo_coupled_mpt L < yukon ↔ L ≤ 6507) ∧
      4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧
      yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508) :=
  ⟨four_heap_non_vacuous_and_tight, four_memo_non_vacuous_and_tight⟩

/-- 5. Zero-clock `StackRemove` simulation for `Skip` and `Tick` (`compCorrectSkipZ` and
`compCorrectTickZ`). -/
theorem stack_remove_skip_and_tick_zero_clock_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool) :
    (∀ (_hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
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
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  stack_remove_skip_and_tick_zero_clock_non_vacuous_and_tight source result postSource target
    pointer bounds jump

/-- 6. Zero-clock `StackRemove` simulation for `Inst` (`compCorrectInstZ`). -/
theorem stack_remove_inst_zero_clock_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : HolInst width)
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.inst instruction) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) :=
  stack_remove_inst_zero_clock_non_vacuous_and_tight source result postSource target pointer bounds
    jump instruction hypothesis

/-- 7. Zero-clock `StackRemove` simulation for `StackLoad` and `StackStore`
(`compCorrectStackLoadZ` and `compCorrectStackStoreZ`). -/
theorem stack_remove_load_and_store_zero_clock_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool) :
    (∀ (_hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
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
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  stack_remove_load_and_store_zero_clock_non_vacuous_and_tight source result postSource target
    register count pointer bounds jump

/-- 8. Zero-clock `StackRemove` simulation for `StackFree` and `StackAlloc` (`compCorrectStackFreeZ`
and `compCorrectStackAllocZ` with `clock ≤ 1` and `clock = 0` outside stack-overflow). -/
theorem stack_remove_free_and_alloc_zero_clock_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool) :
    (∀ (_hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
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
         | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  ⟨fun h => stack_remove_free_zero_clock_non_vacuous_and_tight source result postSource target
     count pointer bounds jump h,
   fun h => stack_remove_alloc_zero_clock_non_vacuous_and_tight source result postSource target
     count pointer bounds jump h⟩

/-- 9. Strictly increasing 68-budget portfolio `< 900,719,925,474` and its conditional finite
certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)`. -/
theorem sixty_eight_budget_portfolio_and_certificates_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SixtyEightShape ∧ ClaimPayloads ∧ yukon = 900719925474 ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(sixty_eight_budget_certificates_non_vacuous_and_tight cert).1,
   (sixty_eight_budget_certificates_non_vacuous_and_tight cert).2.1,
   rfl,
   (sixty_eight_budget_certificates_non_vacuous_and_tight cert).2.2⟩

/-- 10. Unified campaign bridge combining the `619,060,000`-tick coupled-MPT write saving
(`224,366,249,693` heap and `195,035,480,749` memoized), exact `1×` / `4×` Yukon thresholds,
`StackRemove` zero-clock base-case guarantees, and the 68-budget portfolio with conditional finite
certificates. -/
theorem end_to_end_coupled_mpt_stack_remove_zero_campaign_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (13000000000 - 130000 * 95238 = 619060000 ∧
      block_total_coupled_mpt = 224366249693 ∧
      block_total_memo_coupled_mpt = 195035480749) ∧
    (1 * coupled block_total_coupled_mpt 38817 < yukon ∧
      yukon ≤ 1 * coupled block_total_coupled_mpt 38818 ∧
      1 * coupled block_total_memo_coupled_mpt 40284 < yukon ∧
      yukon ≤ 1 * coupled block_total_memo_coupled_mpt 40285 ∧
      4 * coupled block_total_coupled_mpt 5040 < yukon ∧
      yukon ≤ 4 * coupled block_total_coupled_mpt 5041 ∧
      4 * coupled block_total_memo_coupled_mpt 6507 < yukon ∧
      yukon ≤ 4 * coupled block_total_memo_coupled_mpt 6508) ∧
    (SixtyEightShape ∧ ClaimPayloads ∧ yukon = 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨coupling_gain,
    coupled_mpt_totals_non_vacuous_and_tight.1,
    coupled_mpt_totals_non_vacuous_and_tight.2.1⟩,
   ⟨one_heap_non_vacuous_and_tight.2.1,
    one_heap_non_vacuous_and_tight.2.2,
    one_memo_non_vacuous_and_tight.2.1,
    one_memo_non_vacuous_and_tight.2.2,
    four_heap_non_vacuous_and_tight.2.1,
    four_heap_non_vacuous_and_tight.2.2,
    four_memo_non_vacuous_and_tight.2.1,
    four_memo_non_vacuous_and_tight.2.2⟩,
   ⟨(sixty_eight_budget_certificates_non_vacuous_and_tight cert).1,
    (sixty_eight_budget_certificates_non_vacuous_and_tight cert).2.1,
    rfl⟩,
   (sixty_eight_budget_certificates_non_vacuous_and_tight cert).2.2⟩

end InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroCampaignBridge
