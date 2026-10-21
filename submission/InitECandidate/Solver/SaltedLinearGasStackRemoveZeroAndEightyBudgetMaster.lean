import InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
import InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
import InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Synthesis under the imported hand cost estimates and the explicit assumption
of probe runs at most eight. Salting alone does not ensure that assumption.
The arithmetic envelopes are not semantic runtime certificates; finite semantic
certificates remain conditional on the base certificate. ClockOk allows zero
additional clock except at most one tick for a final halt. -/
namespace InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev Previous := CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio
def portfolio : List Nat := Previous ++ [880629318289, 880629318290]
def EightyShape : Prop :=
  portfolio.length = 80 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 78 = Previous ∧
  portfolio.drop 78 = [880629318289, 880629318290] ∧
  portfolio.getLast? = some 880629318290 ∧ yukon = 900719925474

theorem panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 = true :=
  StackRemoveNoStoreConstsZeroExtraClock.Pancake.panToStackAlloc_bodies_StackNoSt arch prog wc ac perf info

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
  StackRemoveNoStoreConstsZeroExtraClock.Pancake.panToStackRemove_body_zeroExtraClock arch prog wc ac perf info

theorem clockOk_rejects_non_vacuous_and_tight {width : Nat} [NeZero width]
    (w : WordLocW width) :
    ¬ ClockOk (width := width) 1 none ∧ ¬ ClockOk 2 (some (.halt w)) :=
  ⟨StackRemoveNoStoreConstsZeroExtraClock.Pancake.clockOk_rejects_one_none,
   StackRemoveNoStoreConstsZeroExtraClock.Pancake.clockOk_rejects_two_halt w⟩

theorem salted_per_unit_and_quad_vs_lin_non_vacuous_and_tight :
    (60 * 8 * 2 ≤ 1000) ∧
    (2000000 * 2000000 / 40 = 100000000000 ∧ saltedTable 2000000 = 2000000000 ∧
    3800000 * 3800000 / 40 = 361000000000 ∧ saltedTable 3800000 = 3800000000) :=
  ⟨GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.per_unit, GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.quad_vs_lin⟩

theorem salted_envelopes_and_main_values_non_vacuous_and_tight :
    (156088992805 - 100000000000 + 2000000000 = 58088992805 ∧
    467569086329 - 361000000000 + 3800000000 = 110369086329) ∧
    (salted200 = 102485906743) ∧
    (salted380 = 154766000267) :=
  ⟨GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.salted_env, GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.salted200_val, GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.salted380_val⟩

theorem salted_main_slopes_non_vacuous_and_tight :
    (8 * 102485906743 < yukon ∧ yukon - 8 * 102485906743 = 80832671530 ∧
    yukon < 9 * 102485906743) ∧
    (5 * 154766000267 < yukon ∧ yukon - 5 * 154766000267 = 126889924139 ∧
    yukon < 6 * 154766000267) :=
  ⟨GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.slope200, GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.slope380⟩

theorem salt_gain_and_per_unit_slack_non_vacuous_and_tight :
    (100000000000 - 2000000000 = 98000000000 ∧
    361000000000 - 3800000000 = 357200000000) ∧
    (8 * (200485906743 - 100000000000 + 6052 * 2000000) < yukon ∧
      yukon < 8 * (200485906743 - 100000000000 + 6053 * 2000000) ∧
    5 * (511966000267 - 361000000000 + 7678 * 3800000) < yukon ∧
      yukon < 5 * (511966000267 - 361000000000 + 7679 * 3800000)) :=
  ⟨GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.salt_gain, GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster.per_unit_slack⟩

theorem main_subsystem_table_non_vacuous_and_tight :
    gasEnv200 = 156088992805 ∧ witnessMpt = 38946487944 ∧
    postEvm = 4859866650 ∧ prologue = 268435424 ∧
    withdrawals16 = 2113920 ∧ balRlp = 300000000 ∧ requests = 20000000 ∧
    output = 10000 ∧ restTerms = 5450425994 ∧
    main200 = gasEnv200 + witnessMpt + postEvm + prologue + withdrawals16 +
      balRlp + requests + output :=
  CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.main_subsystem_table_non_vacuous_and_tight

theorem bal_bound_non_vacuous_and_tight (k : Nat) (h : 2000 * k ≤ 380000000) :
    k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp ∧ balRlp = 300000000 :=
  CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.bal_bound_non_vacuous_and_tight k h

theorem user_sections_and_base_cases_zero_clock_non_vacuous_and_tight :
    (NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (((∀ {width : Nat} [NeZero width] {C F : Type}
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
       | _ => stateRelHOL jump bounds pointer postSource postTarget)))) :=
  ⟨CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight,
   CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight⟩

theorem eighty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    EightyShape := by
  unfold EightyShape
  decide

theorem eighty_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨eighty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (eighty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight
#print axioms panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight
#print axioms clockOk_rejects_non_vacuous_and_tight
#print axioms salted_per_unit_and_quad_vs_lin_non_vacuous_and_tight
#print axioms salted_envelopes_and_main_values_non_vacuous_and_tight
#print axioms salted_main_slopes_non_vacuous_and_tight
#print axioms salt_gain_and_per_unit_slack_non_vacuous_and_tight
#print axioms main_subsystem_table_non_vacuous_and_tight
#print axioms bal_bound_non_vacuous_and_tight
#print axioms user_sections_and_base_cases_zero_clock_non_vacuous_and_tight
#print axioms eighty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms eighty_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SaltedLinearGasStackRemoveZeroAndEightyBudgetMaster
