import InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
import InitECandidate.Solver.SelfContainedOpcodeTableCountAllSaltedAndEightyBudgetMaster
import InitECandidate.Solver.OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_223: exact arithmetic in the imported hand-counted nodedb/MPT model,
full self-contained compiler simulations, and 82 conditional finite certificates.
The cost model assumes bounded probe runs and memoized decoding; salting alone
is not a worst-case probe guarantee. Arithmetic estimates are not semantic
runtime certificates. Finite certificates remain conditional on the base
semantic certificate. ClockOk retains the one-tick final-halt allowance and
StackAlloc retains its exceptional one-tick allowance. -/
namespace InitECandidate.Solver.SelfContainedSaltedNodedbTwentySevenXAndEightyTwoBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open _root_.InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native

abbrev portfolio := OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.portfolio
abbrev EightyTwoShape := OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.EightyTwoShape

/-- Dissection, already-salted probes and the recounted per-visit charge. -/
theorem dissect_probes_salted_visit_cost_non_vacuous_and_tight :
    (decodeMemo + probesR8 + (20036870848 - 619060000) = 38946487944 ∧
     probesR8 = 8589933568) ∧
    (probesR8 = 2 * 8 * (16 * 33554428)) ∧
    (30 + 633 = 663 ∧ 663 < 1000) :=
  ⟨dissect, probes_salted, visit_cost⟩

/-- Exact build, walk, root, witness/MPT and post-EVM rows. -/
theorem rows_200_wm_vals_post_val_non_vacuous_and_tight :
    (buildNodedb = 3038649506 ∧ walks 200000000 = 130000000 ∧
     rootTicks 200000000 = 4104281610) ∧
    (witnessMptSalted 200000000 = 26801608212 ∧
     witnessMptSalted 380000000 = 30612453042) ∧
    postEvmSalted = 681400462 :=
  ⟨rows_200, wm_vals, post_val⟩

/-- Both main totals and their adjacent accepted/rejected integer slopes. -/
theorem main200_main380_slope_non_vacuous_and_tight :
    (main200 = 32905132252 ∧ 27 * main200 < yukon ∧ yukon < 28 * main200) ∧
    (main380 = 41010777082 ∧ 21 * main380 < yukon ∧ yukon < 22 * main380) :=
  ⟨main200_slope, main380_slope⟩

/-- The 30x target fails, with memo decoding and probes dominating the cost. -/
theorem no_thirty_dominant_non_vacuous_and_tight :
    (yukon / 30 = 30023997515 ∧ yukon < 30 * main200) ∧
    100 * (decodeMemo + probesR8) > 59 * main200 :=
  ⟨no_thirty, dominant⟩

/-- Exact one-probe hypothetical total and its 35x/36x boundary. -/
theorem r1_lever_non_vacuous_and_tight :
    main200 - probesR8 + 2 * 1 * 536870848 = 25388940380 ∧
    35 * 25388940380 < yukon ∧ yukon < 36 * 25388940380 := r1_lever

theorem panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 = true :=
  OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight arch prog wc ac perf info

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
  OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight arch prog wc ac perf info

theorem panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight :
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  SelfContainedOpcodeTableCountAllSaltedAndEightyBudgetMaster.panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

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
  SelfContainedOpcodeTableCountAllSaltedAndEightyBudgetMaster.base_cases_zero_clock_non_vacuous_and_tight

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
  SelfContainedOpcodeTableCountAllSaltedAndEightyBudgetMaster.stack_space_clock_non_vacuous_and_tight

theorem eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    EightyTwoShape :=
  OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight

theorem eighty_two_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    EightyTwoShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  OpcodeTableCountAllSaltedAndEightyTwoBudgetMaster.eighty_two_budget_certificates_non_vacuous_and_tight cert

#print axioms dissect_probes_salted_visit_cost_non_vacuous_and_tight
#print axioms rows_200_wm_vals_post_val_non_vacuous_and_tight
#print axioms main200_main380_slope_non_vacuous_and_tight
#print axioms no_thirty_dominant_non_vacuous_and_tight
#print axioms r1_lever_non_vacuous_and_tight
#print axioms panToStackAlloc_bodies_StackNoSt_non_vacuous_and_tight
#print axioms panToStackRemove_body_zeroExtraClock_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight
#print axioms base_cases_zero_clock_non_vacuous_and_tight
#print axioms stack_space_clock_non_vacuous_and_tight
#print axioms eighty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms eighty_two_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedSaltedNodedbTwentySevenXAndEightyTwoBudgetMaster
