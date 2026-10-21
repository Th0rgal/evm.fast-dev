import InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound
import InitECandidate.Solver.PrologueSecp256k1AndSeventyBudgetBridge
import InitECandidate.Solver.SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Exact arithmetic under the imported conservative guest cost estimates.
These estimates are not semantic runtime certificates. Finite certificates below
are conditional on the base semantic certificate. StackRemove zero clock means
zero additional clock; exceptional allocation may need one tick. -/
namespace InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (coupled excess)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm



abbrev maxInput := GuestSszHtrHeadersAndCompleteMainBound.maxInput
abbrev nwdMax := GuestSszHtrHeadersAndCompleteMainBound.nwdMax
abbrev r1 := GuestSszHtrHeadersAndCompleteMainBound.r1
abbrev r4 := GuestSszHtrHeadersAndCompleteMainBound.r4
abbrev Previous := SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318283, 880629318284]
def SeventyFourShape : Prop :=
  portfolio.length = 74 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 72 = Previous ∧
  portfolio.drop 72 = [880629318283, 880629318284] ∧
  portfolio.getLast? = some 880629318284 ∧ yukon = 900719925474

theorem prologue_val_non_vacuous_and_tight :
    maxInput = 134217712 ∧ 2 * maxInput = 268435424 := by
  exact ⟨rfl, GuestSszHtrHeadersAndCompleteMainBound.prologue_val⟩

theorem rho_inside_non_vacuous_and_tight :
    2 ≤ 188 ∧ 2 ≤ 5003 ∧
    (∀ rate : Nat, rate * maxInput ≤ r4 ↔ rate ≤ 188) ∧
    (∀ rate : Nat, rate * maxInput ≤ r1 ↔ rate ≤ 5003) ∧
    188 * maxInput ≤ r4 ∧ r4 < 189 * maxInput ∧
    5003 * maxInput ≤ r1 ∧ r1 < 5004 * maxInput := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · intro rate; unfold maxInput GuestSszHtrHeadersAndCompleteMainBound.maxInput r4 GuestSszHtrHeadersAndCompleteMainBound.r4; omega
  · intro rate; unfold maxInput GuestSszHtrHeadersAndCompleteMainBound.maxInput r1 GuestSszHtrHeadersAndCompleteMainBound.r1; omega
  · decide

theorem nwd_rlp_ceiling_non_vacuous_and_tight :
    nwdMax = 335544 ∧
    (∀ n : Nat, 25 * n ≤ 8388608 ↔ n ≤ nwdMax) ∧
    25 * nwdMax ≤ 8388608 ∧ 8388608 < 25 * (nwdMax + 1) := by
  refine ⟨rfl, ?_, by decide⟩
  intro n; unfold nwdMax GuestSszHtrHeadersAndCompleteMainBound.nwdMax; omega

theorem close_1x_linear_non_vacuous_and_tight :
    r1 - 2 * maxInput - 200000 * nwdMax = 604116573707 ∧
    (∀ n : Nat, n ≤ nwdMax → 200000 * n ≤ 67108800000) ∧
    200000 * nwdMax = 67108800000 ∧
    2 * maxInput + 200000 * nwdMax + 604116573707 = r1 := by
  exact ⟨GuestSszHtrHeadersAndCompleteMainBound.close_1x_linear, GuestSszHtrHeadersAndCompleteMainBound.wd_linear, by decide⟩

theorem close_1x_quad_non_vacuous_and_tight :
    nwdMax * (nwdMax - 1) = 112589440392 ∧
    (∀ f : Nat, f * 112589440392 ≤ 604116573707 ↔ f ≤ 5) ∧
    5 * 112589440392 ≤ 604116573707 ∧
    604116573707 < 6 * 112589440392 := by
  refine ⟨by decide, ?_, GuestSszHtrHeadersAndCompleteMainBound.close_1x_quad⟩
  intro f; omega

theorem fourx_wd_threshold_non_vacuous_and_tight :
    (∀ n : Nat, 2 * maxInput + 200000 * n ≤ r4 ↔ n ≤ 125080) ∧
    2 * maxInput + 200000 * 125080 ≤ r4 ∧
    r4 < 2 * maxInput + 200000 * 125081 ∧
    r4 < 2 * maxInput + 200000 * nwdMax := by
  refine ⟨?_, GuestSszHtrHeadersAndCompleteMainBound.fourx_wd_threshold.1, GuestSszHtrHeadersAndCompleteMainBound.fourx_wd_threshold.2, GuestSszHtrHeadersAndCompleteMainBound.fourx_fails⟩
  intro n; unfold maxInput GuestSszHtrHeadersAndCompleteMainBound.maxInput r4 GuestSszHtrHeadersAndCompleteMainBound.r4; omega

theorem post_evm_and_residual_margins_non_vacuous_and_tight :
    30000 * 16668 = 500040000 ∧ 2 * 130000 * 16666 = 4333160000 ∧
    50 * 533333 = 26666650 ∧
    PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.post_evm = 4859866650 ∧
    900719925474 - PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.block_total = r1 ∧
    900719925474 / 4 - PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.block_total_memo = r4 := by
  exact ⟨PrologueSecp256k1AndSeventyBudgetBridge.post_evm_bridge_non_vacuous_and_tight.1,
    PrologueSecp256k1AndSeventyBudgetBridge.post_evm_bridge_non_vacuous_and_tight.2.1,
    PrologueSecp256k1AndSeventyBudgetBridge.post_evm_bridge_non_vacuous_and_tight.2.2.1,
    PrologueSecp256k1AndSeventyBudgetBridge.post_evm_bridge_non_vacuous_and_tight.2.2.2,
    PrologueSecp256k1AndSeventyBudgetBridge.one_margin_non_vacuous_and_tight.1,
    PrologueSecp256k1AndSeventyBudgetBridge.fourfold_memo_margin_bridge_non_vacuous_and_tight.1⟩

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster.stack_space_clock_non_vacuous_and_tight


/-- Exactly 74 strictly increasing budgets, preserving the previous 72. -/
theorem seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SeventyFourShape := by
  unfold SeventyFourShape
  decide

/-- Conditional finite certificates for every budget, using the baseline ROM. -/
theorem seventy_four_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    SeventyFourShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms prologue_val_non_vacuous_and_tight
#print axioms rho_inside_non_vacuous_and_tight
#print axioms nwd_rlp_ceiling_non_vacuous_and_tight
#print axioms close_1x_linear_non_vacuous_and_tight
#print axioms close_1x_quad_non_vacuous_and_tight
#print axioms fourx_wd_threshold_non_vacuous_and_tight
#print axioms post_evm_and_residual_margins_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms seventy_four_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster
