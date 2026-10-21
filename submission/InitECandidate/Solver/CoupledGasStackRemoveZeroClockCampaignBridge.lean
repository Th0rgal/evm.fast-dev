import InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster
import InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock
import InitECandidate.Solver.FullBlockTransientProbesAndSixtyTwoBudgetBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.CoupledGasStackRemoveZeroClockCampaignBridge`

Wave 5 bridge (`W5_180`) unifying:
* `GuestCoupledGasFullBlockWithProbesAndTransientMaster` (`12/12` tight): exact absorption of `ts+64`
  under the shared `200M` gas budget (`general_side_regime_absorption`), zero net excess for
  `L ≤ 5,000`, and exact thresholds `L_max = 38,786 / 40,253` at `1×` Yukon and
  `L_max = 5,009 / 6,476` at `4×` Yukon;
* `StackRemoveAllocFreeAndBaseCasesZeroClock` (`89/89` tight): zero-clock simulation guarantees
  (`clock = 0`) for `StackRemove` base cases (`compCorrectSkipZ`, `compCorrectTickZ`,
  `compCorrectInstZ`, `compCorrectStackLoadZ`, `compCorrectStackStoreZ`, `compCorrectStackFreeZ`,
  and `compCorrectStackAllocZ` with `clock = 0` outside stack-overflow);
* `FullBlockTransientProbesAndSixtyTwoBudgetBridge` (`10/10` tight): the strictly increasing
  62-budget portfolio `< 900,719,925,474` and its conditional finite certificates
  `InitE.Certificate (baselineWithFiniteK K) (.finite K)`.

No `InitECandidate.Proofs.Bounded*` imports.
-/

namespace InitECandidate.Solver.CoupledGasStackRemoveZeroClockCampaignBridge

open InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock
open InitECandidate.Solver.FullBlockTransientProbesAndSixtyTwoBudgetBridge
open InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster (subHeap subMemo)
open InitECandidate.Solver.WitnessResolveBlockTotalTicksAndSixtyTwoBudgetMaster
  (portfolio SixtyTwoShape ClaimPayloads certificates_non_vacuous_and_tight)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- 1. Shared-budget side-regime absorption (`general_side_regime_absorption`): for `L ≤ 5,000`,
`ts+64` adds `0` net ticks and leaves the full block subtotals unchanged (`224,985,309,693` and
`195,654,540,749`), with first positive excess at `L = 5,001`. -/
theorem coupled_gas_side_regime_absorption_non_vacuous_and_tight
    (L n u B blk : Nat) (hL : L ≤ 5000) (hu : n ≤ u) (hS : B + u ≤ 2000000)
    (hblk : 40 * blk ≤ B * B) :
    blk + 10 * L * n ≤ 100000000000 ∧
      excess L = 0 ∧
      coupled subHeap L = 224985309693 ∧
      coupled subMemo L = 195654540749 ∧
      excess 5001 = 20000000 :=
  ⟨absorbed L n u B blk hL hu hS hblk,
   excess_zero L hL,
   (block_unchanged L hL).1,
   (block_unchanged L hL).2,
   excess_first⟩

/-- 2. Exact coupled `1×` Yukon thresholds: `L_max = 38,786` (heap) and `L_max = 40,253`
(memoized). -/
theorem coupled_lmax_one_yukon_thresholds_non_vacuous_and_tight :
    (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787) ∧
      (coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254) :=
  ⟨GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax1_heap,
   GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax1_memo⟩

/-- 3. Exact coupled `4×` Yukon thresholds: `L_max = 5,009` (heap) and `L_max = 6,476`
(memoized), plus unsalted failure at `L = 158,162`. -/
theorem coupled_lmax_four_yukon_thresholds_non_vacuous_and_tight :
    (4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010) ∧
      (4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477) ∧
      (40253 < 158162 ∧ yukon < coupled subMemo 158162 ∧ yukon < coupled subHeap 158162) :=
  ⟨GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax4_heap,
   GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax4_memo,
   unsalted_still_fails⟩

/-- 4. Zero-clock `StackRemove` simulation for `Skip` and `Tick` (`compCorrectSkipZ` and
`compCorrectTickZ`). -/
theorem stack_remove_skip_and_tick_zero_clock_non_vacuous_and_tight
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
  ⟨fun h => Atoms.compCorrectSkipZ source result postSource target pointer bounds jump h,
   fun h => Control.compCorrectTickZ source result postSource target pointer bounds jump h⟩

/-- 5. Zero-clock `StackRemove` simulation for `Inst` (`compCorrectInstZ`). -/
theorem stack_remove_inst_zero_clock_non_vacuous_and_tight
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
  Instructions.compCorrectInstZ source result postSource target pointer bounds jump instruction
    hypothesis

/-- 6. Zero-clock `StackRemove` simulation for `StackLoad` and `StackStore`
(`compCorrectStackLoadZ` and `compCorrectStackStoreZ`). -/
theorem stack_remove_load_and_store_zero_clock_non_vacuous_and_tight
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
  ⟨fun h => StackMemory.compCorrectStackLoadZ source result postSource target register count pointer bounds jump h,
   fun h => StackMemory.compCorrectStackStoreZ source result postSource target register count pointer bounds jump h⟩

/-- 7. Zero-clock `StackRemove` simulation for `StackFree` (`compCorrectStackFreeZ`). -/
theorem stack_remove_free_zero_clock_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackFree count) : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) :=
  StackSpace.compCorrectStackFreeZ source result postSource target count pointer bounds jump
    hypothesis

/-- 8. `StackAlloc` simulation (`compCorrectStackAllocZ`) with `clock ≤ 1` and `clock = 0`
whenever `result = none` (outside stack-overflow). -/
theorem stack_remove_alloc_zero_clock_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackAlloc count) : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F),
      clock ≤ 1 ∧ (result = none → clock = 0) ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) :=
  StackSpace.compCorrectStackAllocZ source result postSource target count pointer bounds jump
    hypothesis

/-- 9. Strictly increasing 62-budget portfolio `< 900,719,925,474` and its conditional finite
certificates `InitE.Certificate (baselineWithFiniteK K) (.finite K)`. -/
theorem sixty_two_budget_portfolio_and_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SixtyTwoShape ∧ ClaimPayloads ∧ yukon = 900719925474 ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨portfolio_62_non_vacuous_and_tight.1,
   portfolio_62_non_vacuous_and_tight.2,
   rfl,
   (certificates_non_vacuous_and_tight cert).2⟩

/-- 10. Unified campaign bridge combining coupled-gas `ts+64` absorption (`L ≤ 5,000` and exact
`1×` / `4×` Yukon thresholds), `StackRemove` zero-clock base-case simulations, and the 62-budget
portfolio with conditional finite certificates. -/
theorem coupled_gas_stack_remove_zero_clock_campaign_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (∀ L, L ≤ 5000 →
      excess L = 0 ∧ coupled subHeap L = 224985309693 ∧ coupled subMemo L = 195654540749) ∧
    (coupled subHeap 38786 < yukon ∧ yukon ≤ coupled subHeap 38787 ∧
      coupled subMemo 40253 < yukon ∧ yukon ≤ coupled subMemo 40254 ∧
      4 * coupled subHeap 5009 < yukon ∧ yukon ≤ 4 * coupled subHeap 5010 ∧
      4 * coupled subMemo 6476 < yukon ∧ yukon ≤ 4 * coupled subMemo 6477) ∧
    (subHeap = 224985309693 ∧ subMemo = 195654540749 ∧
      SixtyTwoShape ∧ ClaimPayloads ∧ yukon = 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨fun L hL => ⟨excess_zero L hL, (block_unchanged L hL).1, (block_unchanged L hL).2⟩,
   ⟨GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax1_heap.1,
    GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax1_heap.2,
    GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax1_memo.1,
    GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax1_memo.2,
    GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax4_heap.1,
    GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax4_heap.2,
    GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax4_memo.1,
    GuestCoupledGasFullBlockWithProbesAndTransientMaster.lmax4_memo.2⟩,
   ⟨subtotals_non_vacuous_and_tight.1,
    subtotals_non_vacuous_and_tight.2,
    portfolio_62_non_vacuous_and_tight.1,
    portfolio_62_non_vacuous_and_tight.2,
    rfl⟩,
   (certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.CoupledGasStackRemoveZeroClockCampaignBridge
