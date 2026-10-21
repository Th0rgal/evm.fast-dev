import InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster
import InitECandidate.Solver.SelfContainedSaltedLinearGasAndSeventyEightBudgetMaster
import InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_218: exact arithmetic for the imported hand-counted opcode/table model,
full self-contained compiler simulation contracts, and 80 conditional finite
certificates. The all-salted model assumes probe runs bounded by eight;
salting alone does not establish a worst-case run bound. Arithmetic estimates
are not semantic runtime certificates. Finite certificates remain conditional
on the base semantic certificate. ClockOk allows at most one extra tick for a
final halt; the base simulations preserve their full post-state relations and
the exceptional allocation allowance. -/
namespace InitECandidate.Solver.SelfContainedOpcodeTableCountAllSaltedAndEightyBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestOpcodeTableCountAndAllTablesSaltedMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev portfolio := SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.portfolio
abbrev EightyShape := SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.EightyShape

/-- Counted opcode maximum and exact salted-operation/unit charges. -/
theorem finds_max_unit_val_non_vacuous_and_tight :
    (1 + 2 + 2 + 2 = 7 ∧ 1 ≤ 7 ∧ 3 ≤ 7 ∧ 1 + 5 ≤ 7) ∧
    (opTicks 8 = 28 ∧ unitTicks = 336) :=
  ⟨finds_max, unit_val⟩

/-- Exact collision decomposition, new envelopes and unchanged non-gas rows. -/
theorem env_split_env_vals_non_vacuous_and_tight :
    (3659564234 + 500000000 + 151929428571 = 156088992805 ∧
     151929428571 = 100000000000 + 51929428571) ∧
    (env200 = 4831564234 ∧ env380 = 9126364234) ∧
    restMain = 44396913938 :=
  ⟨env_split, env_vals, rest_val⟩

/-- Both complete totals and their adjacent passing/failing multipliers. -/
theorem main200_main380_slope_non_vacuous_and_tight :
    (main200AllSalted = 49228478172 ∧ 18 * main200AllSalted < yukon ∧
     yukon < 19 * main200AllSalted) ∧
    (main380AllSalted = 53523278172 ∧ 16 * main380AllSalted < yukon ∧
     yukon < 17 * main380AllSalted) :=
  ⟨main200_slope, main380_slope⟩

/-- Adjacent per-unit and probe-run sensitivity thresholds. -/
theorem unit_slack_run_slack_non_vacuous_and_tight :
    (18 * (3659564234 + 500000000 + 741 * 2000000 + restMain) < yukon ∧
     yukon ≤ 18 * (3659564234 + 500000000 + 742 * 2000000 + restMain) ∧
     16 * (59564234 + 18 * 380000000 + 950000000 + 1065 * 3800000 + restMain) < yukon ∧
     yukon ≤ 16 * (59564234 + 18 * 380000000 + 950000000 + 1066 * 3800000 + restMain)) ∧
    (12 * opTicks 24 ≤ 741 ∧ 741 < 12 * opTicks 25) :=
  ⟨unit_slack, run_slack⟩

/-- Exact savings over partial salting, and dominance of the non-gas rows. -/
theorem gain_rest_dominates_non_vacuous_and_tight :
    (102485906743 - 49228478172 = 53257428571 ∧
     154766000267 - 53523278172 = 101242722095) ∧
    10 * restMain > 9 * main200AllSalted :=
  ⟨gain, rest_dominates⟩

theorem panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 = true :=
  SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight arch prog wc ac perf info

theorem panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
        CodeNoSt source →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 pointer →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp jump bounds pointer
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget) :=
  SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight arch prog wc ac perf info

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedSaltedLinearGasAndSeventyEightBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  SelfContainedSaltedLinearGasAndSeventyEightBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  SelfContainedSaltedLinearGasAndSeventyEightBudgetMaster.stack_space_clock_non_vacuous_and_tight

theorem eighty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    EightyShape :=
  SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.eighty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem eighty_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster.eighty_budget_certificates_non_vacuous_and_tight cert

#print axioms finds_max_unit_val_non_vacuous_and_tight
#print axioms env_split_env_vals_non_vacuous_and_tight
#print axioms main200_main380_slope_non_vacuous_and_tight
#print axioms unit_slack_run_slack_non_vacuous_and_tight
#print axioms gain_rest_dominates_non_vacuous_and_tight
#print axioms panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight
#print axioms panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms eighty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms eighty_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedOpcodeTableCountAllSaltedAndEightyBudgetMaster
