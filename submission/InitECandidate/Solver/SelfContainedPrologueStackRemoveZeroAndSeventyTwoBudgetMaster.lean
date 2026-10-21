import InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSixtyEightBudgetBridge
import InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster
import InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact arithmetic under the imported conservative post-EVM unit estimates,
full user-section safety and StackRemove simulation contracts. These estimates
are not PanSem-derived. Zero clock denotes zero additional clock; exceptional
allocation may require one tick. Finite certificates require the base semantic
certificate explicitly. -/
namespace InitECandidate.Solver.SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (coupled excess)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

abbrev postTerms := GuestPrologueTxDecodeSecp256k1AndIndexedMptBound.postTerms
abbrev post_evm := postTerms
abbrev block_total := PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.block_total
abbrev block_total_memo := PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.block_total_memo
abbrev Previous := PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318281, 880629318282]
def SeventyTwoShape : Prop :=
  portfolio.length = 72 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 70 = Previous ∧
  portfolio.drop 70 = [880629318281, 880629318282] ∧
  portfolio.getLast? = some 880629318282 ∧ yukon = 900719925474

theorem tx_count_non_vacuous_and_tight :
    (∀ t : Nat, 12000 * t ≤ 200000000 ↔ t ≤ 16666) ∧
    12000 * 16666 ≤ 200000000 ∧ 200000000 < 12000 * 16667 ∧
    16666 + 2 = 16668 :=
  SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.tx_count_non_vacuous_and_tight

theorem post_evm_terms_non_vacuous_and_tight :
    (∀ t : Nat, t ≤ 16668 → 30000 * t ≤ 500040000) ∧
    (∀ t : Nat, t ≤ 16666 → 2 * 130000 * t ≤ 4333160000) ∧
    (∀ g : Nat, 375 * g ≤ 200000000 → 50 * g ≤ 26666650) ∧
    30000 * 16668 = 500040000 ∧
    2 * 130000 * 16666 = 4333160000 ∧
    (375 * 533333 ≤ 200000000 ∧ 200000000 < 375 * 533334) ∧
    50 * 533333 = 26666650 ∧ postTerms = 4859866650 :=
  SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.post_evm_terms_non_vacuous_and_tight

theorem prologue_one_x_non_vacuous_and_tight :
    676353675781 - postTerms = 671493809131 ∧
    (∀ rate : Nat, rate * 134217712 ≤ 671493809131 ↔ rate ≤ 5003) ∧
    5003 * 134217712 ≤ 671493809131 ∧
    671493809131 < 5004 * 134217712 :=
  SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.prologue_one_x_non_vacuous_and_tight

theorem prologue_four_x_memo_non_vacuous_and_tight :
    30144500619 - postTerms = 25284633969 ∧
    (∀ rate : Nat, rate * 134217712 ≤ 25284633969 ↔ rate ≤ 188) ∧
    188 * 134217712 ≤ 25284633969 ∧
    25284633969 < 189 * 134217712 :=
  SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.prologue_four_x_memo_non_vacuous_and_tight

theorem one_heap_lmax_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled block_total L < yukon ↔ L ≤ 38574) ∧
    1 * coupled block_total 38574 < yukon ∧
    yukon ≤ 1 * coupled block_total 38575 :=
  PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.one_heap_lmax_non_vacuous_and_tight

theorem one_memo_lmax_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled block_total_memo L < yukon ↔ L ≤ 40041) ∧
    1 * coupled block_total_memo 40041 < yukon ∧
    yukon ≤ 1 * coupled block_total_memo 40042 :=
  PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.one_memo_lmax_non_vacuous_and_tight

theorem four_memo_lmax_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupled block_total_memo L < yukon ↔ L ≤ 6264) ∧
    4 * coupled block_total_memo 6264 < yukon ∧
    yukon ≤ 4 * coupled block_total_memo 6265 :=
  PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.four_memo_lmax_non_vacuous_and_tight

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.stack_space_clock_non_vacuous_and_tight

/-- Exactly 72 strictly increasing budgets with an unchanged 70-budget prefix. -/
theorem seventy_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SeventyTwoShape := by
  unfold SeventyTwoShape
  decide

/-- Every finite claim is certified conditional on the base semantic certificate. -/
theorem seventy_two_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventyTwoShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨seventy_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (seventy_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms tx_count_non_vacuous_and_tight
#print axioms post_evm_terms_non_vacuous_and_tight
#print axioms prologue_one_x_non_vacuous_and_tight
#print axioms prologue_four_x_memo_non_vacuous_and_tight
#print axioms one_heap_lmax_non_vacuous_and_tight
#print axioms one_memo_lmax_non_vacuous_and_tight
#print axioms four_memo_lmax_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms seventy_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms seventy_two_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster
