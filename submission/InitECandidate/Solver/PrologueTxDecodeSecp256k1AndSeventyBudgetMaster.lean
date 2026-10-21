import InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
import InitECandidate.Solver.StackRemoveBaseCasesZeroClockAndSixtyFourBudgetBridge
import InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Arithmetic envelope using the imported conservative per-unit post-EVM estimates.
These estimates are not PanSem-derived. Zero clock means zero additional clock;
allocation may require one on exceptional results. All finite certificates are
conditional on the semantic base certificate. -/
namespace InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster
open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (coupled excess)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev post_evm := GuestPrologueTxDecodeSecp256k1AndIndexedMptBound.postTerms
def block_total : Nat :=
  EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.block_total_coupled_mpt + post_evm
def block_total_memo : Nat :=
  EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.block_total_memo_coupled_mpt + post_evm
abbrev Previous := EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318279, 880629318280]
def SeventyShape : Prop :=
  portfolio.length = 70 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 68 = Previous ∧
  portfolio.drop 68 = [880629318279, 880629318280] ∧
  portfolio.getLast? = some 880629318280 ∧ yukon = 900719925474

/-- Attained intrinsic-gas bound, including exactly two system transactions. -/
theorem transaction_ceiling_non_vacuous_and_tight :
    (∀ t : Nat, 12000 * t ≤ 200000000 ↔ t ≤ 16666) ∧
    12000 * 16666 ≤ 200000000 ∧ 200000000 < 12000 * 16667 ∧
    16666 + 2 = 16668 := by
  refine ⟨?_, by decide⟩
  intro t
  omega

/-- Exact post-EVM terms, with attained bounds for all three components. -/
theorem post_evm_non_vacuous_and_tight :
    (∀ t : Nat, t ≤ 16668 → 30000 * t ≤ 500040000) ∧
    (∀ t : Nat, t ≤ 16666 → 2 * 130000 * t ≤ 4333160000) ∧
    (∀ g : Nat, 375 * g ≤ 200000000 → 50 * g ≤ 26666650) ∧
    30000 * 16668 = 500040000 ∧ 2 * 130000 * 16666 = 4333160000 ∧
    375 * 533333 ≤ 200000000 ∧ 200000000 < 375 * 533334 ∧
    50 * 533333 = 26666650 ∧ post_evm = 4859866650 := by
  exact ⟨GuestPrologueTxDecodeSecp256k1AndIndexedMptBound.secp_total,
    GuestPrologueTxDecodeSecp256k1AndIndexedMptBound.tries_total,
    GuestPrologueTxDecodeSecp256k1AndIndexedMptBound.bloom_total, by decide⟩

theorem block_totals_non_vacuous_and_tight :
    block_total = 229226116343 ∧ block_total_memo = 199895347399 ∧
    block_total - block_total_memo = 29330768944 := by decide

theorem fourfold_heap_refuted_non_vacuous_and_tight :
    yukon / 4 = 225179981368 ∧ 225179981368 < block_total ∧
    yukon < 4 * block_total ∧ 4 * block_total - yukon = 16184539898 := by decide

theorem fourfold_memo_margin_non_vacuous_and_tight :
    block_total_memo < yukon / 4 ∧
    yukon / 4 - block_total_memo = 25284633969 ∧
    188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712 ∧
    4 * block_total_memo < yukon := by decide

/-- Exact interval, attained endpoint and first rejected integer. -/
theorem one_heap_lmax_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled block_total L < yukon ↔ L ≤ 38574) ∧
    1 * coupled block_total 38574 < yukon ∧
    yukon ≤ 1 * coupled block_total 38575 := by
  constructor
  · intro L
    change 1 * (229226116343 + (10 * L - 50000) * 2000000) < 900719925474 ↔ L ≤ 38574
    omega
  · decide

/-- Exact interval, attained endpoint and first rejected integer. -/
theorem one_memo_lmax_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled block_total_memo L < yukon ↔ L ≤ 40041) ∧
    1 * coupled block_total_memo 40041 < yukon ∧
    yukon ≤ 1 * coupled block_total_memo 40042 := by
  constructor
  · intro L
    change 1 * (199895347399 + (10 * L - 50000) * 2000000) < 900719925474 ↔ L ≤ 40041
    omega
  · decide

/-- Exact interval, attained endpoint and first rejected integer. -/
theorem four_memo_lmax_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupled block_total_memo L < yukon ↔ L ≤ 6264) ∧
    4 * coupled block_total_memo 6264 < yukon ∧
    yukon ≤ 4 * coupled block_total_memo 6265 := by
  constructor
  · intro L
    change 4 * (199895347399 + (10 * L - 50000) * 2000000) < 900719925474 ↔ L ≤ 6264
    omega
  · decide

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Imported full StackRemove simulation contracts, including post-state relations. -/
theorem base_cases_zero_clock_non_vacuous_and_tight :
    ((∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) :=
  ⟨EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.skip_tick_inst_zero_clock_non_vacuous_and_tight,
   EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.stack_load_store_zero_clock_non_vacuous_and_tight⟩

/-- Imported full StackRemove simulation contracts, including post-state relations. -/
theorem stack_space_clock_non_vacuous_and_tight :
    ((∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget))) :=
  ⟨EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.stack_free_zero_clock_non_vacuous_and_tight,
   EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.stack_alloc_zero_clock_non_vacuous_and_tight⟩

/-- Exact 68-budget prefix plus two new budgets, all strictly below Yukon. -/
theorem seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SeventyShape := by
  unfold SeventyShape
  decide

/-- Finite certificates for every budget, conditional on the base execution certificate. -/
theorem seventy_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventyShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms transaction_ceiling_non_vacuous_and_tight
#print axioms post_evm_non_vacuous_and_tight
#print axioms block_totals_non_vacuous_and_tight
#print axioms fourfold_heap_refuted_non_vacuous_and_tight
#print axioms fourfold_memo_margin_non_vacuous_and_tight
#print axioms one_heap_lmax_non_vacuous_and_tight
#print axioms one_memo_lmax_non_vacuous_and_tight
#print axioms four_memo_lmax_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms seventy_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster
