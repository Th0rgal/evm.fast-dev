import InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
import InitECandidate.Solver.SelfContainedCoupledMptStackRemoveZeroAndSixtySixBudgetMaster
import InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_188: exact prologue arithmetic, full user-section safety and StackRemove
base-case simulations, and 68 conditional finite certificates. Per-unit guest
costs are the imported conservative hand estimates, not PanSem execution bounds.
The semantic base certificate and remaining end-to-end obligations stay explicit.
Zero clock means zero additional clock; allocation may need one exceptional tick. -/
namespace InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev postTerms := GuestPrologueTxDecodeSecp256k1AndIndexedMptBound.postTerms
abbrev portfolio := EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.portfolio
abbrev SixtyEightShape := EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.SixtyEightShape
abbrev ClaimPayloads := EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.ClaimPayloads

/-- Sharp user-transaction cap, attained endpoint, first rejection, and system count. -/
theorem tx_count_non_vacuous_and_tight :
    (∀ t : Nat, 12000 * t ≤ 200000000 ↔ t ≤ 16666) ∧
    12000 * 16666 ≤ 200000000 ∧ 200000000 < 12000 * 16667 ∧
    16666 + 2 = 16668 := by
  refine ⟨?_, by decide⟩
  intro t
  omega

/-- Exact maxima for each post-EVM term and their sum, with attained unit caps. -/
theorem post_evm_terms_non_vacuous_and_tight :
    (∀ t : Nat, t ≤ 16668 → 30000 * t ≤ 500040000) ∧
    (∀ t : Nat, t ≤ 16666 → 2 * 130000 * t ≤ 4333160000) ∧
    (∀ g : Nat, 375 * g ≤ 200000000 → 50 * g ≤ 26666650) ∧
    30000 * 16668 = 500040000 ∧
    2 * 130000 * 16666 = 4333160000 ∧
    (375 * 533333 ≤ 200000000 ∧ 200000000 < 375 * 533334) ∧
    50 * 533333 = 26666650 ∧ postTerms = 4859866650 := by
  exact ⟨GuestPrologueTxDecodeSecp256k1AndIndexedMptBound.secp_total,
    GuestPrologueTxDecodeSecp256k1AndIndexedMptBound.tries_total,
    GuestPrologueTxDecodeSecp256k1AndIndexedMptBound.bloom_total, by decide⟩

/-- Exact 1x residual and largest integer per-input-byte rate. -/
theorem prologue_one_x_non_vacuous_and_tight :
    676353675781 - postTerms = 671493809131 ∧
    (∀ rate : Nat, rate * 134217712 ≤ 671493809131 ↔ rate ≤ 5003) ∧
    5003 * 134217712 ≤ 671493809131 ∧
    671493809131 < 5004 * 134217712 := by
  refine ⟨by decide, ?_, by decide⟩
  intro rate
  omega

/-- Exact memoized 4x residual and largest integer per-input-byte rate. -/
theorem prologue_four_x_memo_non_vacuous_and_tight :
    30144500619 - postTerms = 25284633969 ∧
    (∀ rate : Nat, rate * 134217712 ≤ 25284633969 ↔ rate ≤ 188) ∧
    188 * 134217712 ≤ 25284633969 ∧
    25284633969 < 189 * 134217712 := by
  refine ⟨by decide, ?_, by decide⟩
  intro rate
  omega

/-- The heap-only 4x residual fails even at zero prologue; exact deficit. -/
theorem prologue_four_x_heap_fails_non_vacuous_and_tight :
    813731675 < postTerms ∧ postTerms - 813731675 = 4046134975 ∧
    (∀ prologue : Nat, ¬ (postTerms + prologue ≤ 813731675)) := by
  refine ⟨by decide, by decide, ?_⟩
  intro prologue
  change ¬ (4859866650 + prologue ≤ 813731675)
  omega

/-- All user sections exclude section-6 jumps and location values after LabToTarget. -/
theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedNoLocValue6CoupledGasAndSixtyFourBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Full constructor simulation contracts; zero clock means zero additional clock. -/
theorem skip_tick_inst_zero_clock_non_vacuous_and_tight :
    (∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  ⟨@StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms.compCorrectSkipZ, @StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectTickZ, @StackRemoveAllocFreeAndBaseCasesZeroClock.Instructions.compCorrectInstZ⟩

/-- Full constructor simulation contracts; zero clock means zero additional clock. -/
theorem stack_load_store_zero_clock_non_vacuous_and_tight :
    (∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  ⟨@StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory.compCorrectStackLoadZ, @StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory.compCorrectStackStoreZ⟩

/-- Full constructor simulation contracts; zero clock means zero additional clock. -/
theorem stack_free_zero_clock_non_vacuous_and_tight :
    (∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  @StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace.compCorrectStackFreeZ

/-- Full constructor simulation contracts; zero clock means zero additional clock. -/
theorem stack_alloc_zero_clock_non_vacuous_and_tight :
    (∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget)) :=
  @StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace.compCorrectStackAllocZ

/-- Exactly 68 increasing budgets, retaining the 66-budget prefix and finite ceiling. -/
theorem sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SixtyEightShape :=
  EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

/-- Safety, valid finite claims, and all 68 certificates conditional on the base certificate. -/
theorem sixty_eight_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧
    SixtyEightShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight.2,
   EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster.sixty_eight_budget_certificates_non_vacuous_and_tight cert⟩

#print axioms tx_count_non_vacuous_and_tight
#print axioms post_evm_terms_non_vacuous_and_tight
#print axioms prologue_one_x_non_vacuous_and_tight
#print axioms prologue_four_x_memo_non_vacuous_and_tight
#print axioms prologue_four_x_heap_fails_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms skip_tick_inst_zero_clock_non_vacuous_and_tight
#print axioms stack_load_store_zero_clock_non_vacuous_and_tight
#print axioms stack_free_zero_clock_non_vacuous_and_tight
#print axioms stack_alloc_zero_clock_non_vacuous_and_tight
#print axioms sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms sixty_eight_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster
