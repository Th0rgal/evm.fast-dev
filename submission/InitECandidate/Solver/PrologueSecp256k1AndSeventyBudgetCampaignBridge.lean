import InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
import InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroCampaignBridge
import InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.PrologueSecp256k1AndSeventyBudgetCampaignBridge

open InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
open InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroCampaignBridge
open InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (coupled excess)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem tx_ceiling_and_post_evm_breakdown_non_vacuous_and_tight :
    ((∀ t : Nat, 12000 * t ≤ 200000000 ↔ t ≤ 16666) ∧
      12000 * 16666 ≤ 200000000 ∧ 200000000 < 12000 * 16667 ∧
      16666 + 2 = 16668) ∧
    ((∀ t : Nat, t ≤ 16668 → 30000 * t ≤ 500040000) ∧
      (∀ t : Nat, t ≤ 16666 → 2 * 130000 * t ≤ 4333160000) ∧
      (∀ g : Nat, 375 * g ≤ 200000000 → 50 * g ≤ 26666650) ∧
      30000 * 16668 = 500040000 ∧ 2 * 130000 * 16666 = 4333160000 ∧
      375 * 533333 ≤ 200000000 ∧ 200000000 < 375 * 533334 ∧
      50 * 533333 = 26666650 ∧ postTerms = 4859866650) :=
  ⟨transaction_ceiling_non_vacuous_and_tight, post_evm_non_vacuous_and_tight⟩

theorem prologue_residuals_and_post_evm_totals_non_vacuous_and_tight :
    (block_total = 229226116343 ∧ block_total_memo = 199895347399 ∧
      block_total - block_total_memo = 29330768944) ∧
    (676353675781 - postTerms = 671493809131 ∧
      5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712) ∧
    (yukon / 4 = 225179981368 ∧ 225179981368 < block_total ∧
      yukon < 4 * block_total ∧ 4 * block_total - yukon = 16184539898) ∧
    (block_total_memo < yukon / 4 ∧
      yukon / 4 - block_total_memo = 25284633969 ∧
      188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712 ∧
      4 * block_total_memo < yukon) :=
  ⟨block_totals_non_vacuous_and_tight,
   prologue_1x,
   fourfold_heap_refuted_non_vacuous_and_tight,
   fourfold_memo_margin_non_vacuous_and_tight⟩

theorem prologue_one_yukon_lmax_thresholds_non_vacuous_and_tight :
    ((∀ L : Nat, 1 * coupled block_total L < yukon ↔ L ≤ 38574) ∧
      1 * coupled block_total 38574 < yukon ∧
      yukon ≤ 1 * coupled block_total 38575) ∧
    ((∀ L : Nat, 1 * coupled block_total_memo L < yukon ↔ L ≤ 40041) ∧
      1 * coupled block_total_memo 40041 < yukon ∧
      yukon ≤ 1 * coupled block_total_memo 40042) :=
  ⟨one_heap_lmax_non_vacuous_and_tight, one_memo_lmax_non_vacuous_and_tight⟩

theorem prologue_four_yukon_memo_and_coupled_mpt_thresholds_non_vacuous_and_tight :
    ((∀ L : Nat, 4 * coupled block_total_memo L < yukon ↔ L ≤ 6264) ∧
      4 * coupled block_total_memo 6264 < yukon ∧
      yukon ≤ 4 * coupled block_total_memo 6265) ∧
    (((∀ L : Nat, 4 * coupled _root_.InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.block_total_coupled_mpt L < yukon ↔ L ≤ 5040) ∧
      4 * coupled _root_.InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.block_total_coupled_mpt 5040 < yukon ∧
      yukon ≤ 4 * coupled _root_.InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.block_total_coupled_mpt 5041) ∧
     ((∀ L : Nat, 4 * coupled _root_.InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.block_total_memo_coupled_mpt L < yukon ↔ L ≤ 6507) ∧
      4 * coupled _root_.InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.block_total_memo_coupled_mpt 6507 < yukon ∧
      yukon ≤ 4 * coupled _root_.InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.block_total_memo_coupled_mpt 6508)) :=
  ⟨four_memo_lmax_non_vacuous_and_tight, coupled_mpt_four_yukon_thresholds_non_vacuous_and_tight⟩

theorem stack_remove_skip_and_tick_zero_clock_campaign_non_vacuous_and_tight
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
  stack_remove_skip_and_tick_zero_clock_bridge_non_vacuous_and_tight source result postSource target
    pointer bounds jump

theorem stack_remove_inst_zero_clock_campaign_non_vacuous_and_tight
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
  stack_remove_inst_zero_clock_bridge_non_vacuous_and_tight source result postSource target pointer
    bounds jump instruction hypothesis

theorem stack_remove_load_and_store_zero_clock_campaign_non_vacuous_and_tight
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
  stack_remove_load_and_store_zero_clock_bridge_non_vacuous_and_tight source result postSource target
    register count pointer bounds jump

theorem stack_remove_free_and_alloc_zero_clock_campaign_non_vacuous_and_tight
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
  stack_remove_free_and_alloc_zero_clock_bridge_non_vacuous_and_tight source result postSource target
    count pointer bounds jump

theorem seventy_budget_portfolio_and_certificates_campaign_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventyShape ∧ yukon = 900719925474 ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(seventy_budget_certificates_non_vacuous_and_tight cert).1,
   rfl,
   (seventy_budget_certificates_non_vacuous_and_tight cert).2⟩

theorem prologue_secp256k1_and_seventy_budget_campaign_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    (12000 * 16666 ≤ 200000000 ∧ 200000000 < 12000 * 16667 ∧
      16666 + 2 = 16668 ∧ postTerms = 4859866650 ∧
      block_total = 229226116343 ∧ block_total_memo = 199895347399) ∧
    (1 * coupled block_total 38574 < yukon ∧
      yukon ≤ 1 * coupled block_total 38575 ∧
      1 * coupled block_total_memo 40041 < yukon ∧
      yukon ≤ 1 * coupled block_total_memo 40042 ∧
      4 * coupled block_total_memo 6264 < yukon ∧
      yukon ≤ 4 * coupled block_total_memo 6265) ∧
    (SeventyShape ∧ yukon = 900719925474) ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨transaction_ceiling_non_vacuous_and_tight.2.1,
    transaction_ceiling_non_vacuous_and_tight.2.2.1,
    transaction_ceiling_non_vacuous_and_tight.2.2.2,
    post_val,
    block_totals_non_vacuous_and_tight.1,
    block_totals_non_vacuous_and_tight.2.1⟩,
   ⟨one_heap_lmax_non_vacuous_and_tight.2.1,
    one_heap_lmax_non_vacuous_and_tight.2.2,
    one_memo_lmax_non_vacuous_and_tight.2.1,
    one_memo_lmax_non_vacuous_and_tight.2.2,
    four_memo_lmax_non_vacuous_and_tight.2.1,
    four_memo_lmax_non_vacuous_and_tight.2.2⟩,
   ⟨(seventy_budget_certificates_non_vacuous_and_tight cert).1,
    rfl⟩,
   (seventy_budget_certificates_non_vacuous_and_tight cert).2⟩

end InitECandidate.Solver.PrologueSecp256k1AndSeventyBudgetCampaignBridge
