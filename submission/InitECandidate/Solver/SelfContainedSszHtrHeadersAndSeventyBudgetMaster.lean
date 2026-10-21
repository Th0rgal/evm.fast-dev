import InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound
import InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster
import InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_195: SSZ/HTR/header arithmetic, withdrawal thresholds, full compiler
safety and StackRemove base simulations, and 70 conditional finite certificates.
Per-byte and per-withdrawal costs are conservative imported hand estimates,
not execution-derived PanSem bounds. Zero clock denotes additional clock;
allocation retains its exceptional one-tick allowance. The semantic base
certificate remains an explicit assumption. -/
namespace InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev maxInput := GuestSszHtrHeadersAndCompleteMainBound.maxInput
abbrev nwdMax := GuestSszHtrHeadersAndCompleteMainBound.nwdMax
abbrev r1 := GuestSszHtrHeadersAndCompleteMainBound.r1
abbrev r4 := GuestSszHtrHeadersAndCompleteMainBound.r4
abbrev portfolio := PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.portfolio
abbrev SeventyShape := PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.SeventyShape

/-- Exact prologue cost at the maximal input size and rate two. -/
theorem prologue_val_non_vacuous_and_tight :
    maxInput = 134217712 ∧ 2 * maxInput = 268435424 := by decide

/-- Rate two fits both residuals; the integer rate ceilings are exact. -/
theorem rho_inside_non_vacuous_and_tight :
    2 ≤ 188 ∧ 2 ≤ 5003 ∧ 188 * maxInput ≤ r4 ∧ 5003 * maxInput ≤ r1 ∧
    (∀ rate : Nat, rate * maxInput ≤ r4 ↔ rate ≤ 188) ∧
    (∀ rate : Nat, rate * maxInput ≤ r1 ↔ rate ≤ 5003) ∧
    r4 < 189 * maxInput ∧ r1 < 5004 * maxInput := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, by decide⟩
  · intro rate
    change rate * 134217712 ≤ 25284633969 ↔ rate ≤ 188
    omega
  · intro rate
    change rate * 134217712 ≤ 671493809131 ↔ rate ≤ 5003
    omega

/-- Largest feasible withdrawal count from the RLP cap, with both endpoints. -/
theorem nwd_max_non_vacuous_and_tight :
    nwdMax = 335544 ∧ (∀ n : Nat, 25 * n ≤ 8388608 ↔ n ≤ nwdMax) ∧
    25 * nwdMax ≤ 8388608 ∧ 8388608 < 25 * (nwdMax + 1) := by
  refine ⟨rfl, ?_, by decide⟩
  intro n
  change 25 * n ≤ 8388608 ↔ n ≤ 335544
  omega

/-- Exact linear maximum and 1x residual, with closure for every feasible count. -/
theorem close_1x_linear_non_vacuous_and_tight :
    (∀ n : Nat, n ≤ nwdMax → 200000 * n ≤ 67108800000) ∧
    200000 * nwdMax = 67108800000 ∧
    r1 - 2 * maxInput - 200000 * nwdMax = 604116573707 ∧
    2 * maxInput + 200000 * nwdMax + 604116573707 = r1 :=
  ⟨GuestSszHtrHeadersAndCompleteMainBound.wd_linear, by decide⟩

/-- Five unsalted colliding finds fit; six fail at the maximal withdrawal count. -/
theorem close_1x_quad_non_vacuous_and_tight :
    nwdMax * (nwdMax - 1) = 112589440392 ∧
    (∀ f : Nat, f * 112589440392 ≤ 604116573707 ↔ f ≤ 5) ∧
    2 * maxInput + 200000 * nwdMax + 5 * 112589440392 ≤ r1 ∧
    r1 < 2 * maxInput + 200000 * nwdMax + 6 * 112589440392 := by
  refine ⟨by decide, ?_, by decide⟩
  intro f
  omega

/-- Exact 4x memoized withdrawal interval, attained bound and first rejection. -/
theorem fourx_wd_threshold_non_vacuous_and_tight :
    (∀ n : Nat, 2 * maxInput + 200000 * n ≤ r4 ↔ n ≤ 125080) ∧
    2 * maxInput + 200000 * 125080 ≤ r4 ∧
    r4 < 2 * maxInput + 200000 * 125081 := by
  refine ⟨?_, GuestSszHtrHeadersAndCompleteMainBound.fourx_wd_threshold⟩
  intro n
  change 2 * 134217712 + 200000 * n ≤ 25284633969 ↔ n ≤ 125080
  omega

/-- At the RLP maximum even the collision-free 4x envelope fails; exact deficit. -/
theorem fourx_fails_non_vacuous_and_tight :
    r4 < 2 * maxInput + 200000 * nwdMax ∧
    2 * maxInput + 200000 * nwdMax - r4 = 42092601455 := by decide

/-- Full user-section safety after LabToTarget. -/
theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  ⟨SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.skip_tick_inst_zero_clock_non_vacuous_and_tight,
   SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.stack_load_store_zero_clock_non_vacuous_and_tight⟩

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
  ⟨SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.stack_free_zero_clock_non_vacuous_and_tight,
   SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster.stack_alloc_zero_clock_non_vacuous_and_tight⟩

/-- Exactly seventy strictly increasing budgets below the finite Yukon ceiling. -/
theorem seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    SeventyShape :=
  PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

/-- User safety and every finite budget certificate, conditional on the semantic base. -/
theorem seventy_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe ∧ SeventyShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight.2,
   PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.seventy_budget_certificates_non_vacuous_and_tight cert⟩

#print axioms prologue_val_non_vacuous_and_tight
#print axioms rho_inside_non_vacuous_and_tight
#print axioms nwd_max_non_vacuous_and_tight
#print axioms close_1x_linear_non_vacuous_and_tight
#print axioms close_1x_quad_non_vacuous_and_tight
#print axioms fourx_wd_threshold_non_vacuous_and_tight
#print axioms fourx_fails_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms seventy_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyBudgetMaster
