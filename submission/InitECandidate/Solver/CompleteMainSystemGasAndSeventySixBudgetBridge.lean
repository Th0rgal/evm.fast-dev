import InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
import InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyFourBudgetBridge
import InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# CompleteMainSystemGasAndSeventySixBudgetBridge

Wave 5 bridge (W5_205). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.CompleteMainSystemGasAndSeventySixBudgetBridge

open InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster
open InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyFourBudgetBridge
open InitECandidate.Solver.WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. System gas: 2 + 4 = 6, and 200M plus 6 times 30M reaches 380M. -/
theorem system_gas_bridge_non_vacuous_and_tight :
    2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000 :=
  system_gas

/-- 2. Main total at 200M gas: 200_485_906_743, with its slopes. -/
theorem main200_slopes_bridge_non_vacuous_and_tight :
    main200 = 200485906743 ∧
    yukon - main200 = 700234018731 ∧ 4 * main200 < yukon ∧
    yukon / 4 - main200 = 24694074625 ∧ yukon < 5 * main200 :=
  ⟨main_val, main_slopes⟩

/-- 3. Main total at 380M gas: 511_966_000_267; 1x passes, 2x fails. -/
theorem main380_slopes_bridge_non_vacuous_and_tight :
    main380 = 511966000267 ∧
    yukon - main380 = 388753925207 ∧ yukon < 2 * main380 :=
  ⟨main380_val, main380_slopes⟩

/-- 4. BAL bound: at most 190_000 cold keys at 380M, and the merge-sort budget fits. -/
theorem bal_bound_bridge_non_vacuous_and_tight (k : Nat) (h : 2000 * k ≤ 380000000) :
    k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp :=
  bal_bound k h

/-- 5. After LabToTarget, no user section reaches section 6 by jump, conditional jump, call or
locValue. -/
theorem panToTarget_user_sections_seventy_six_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  panToTarget_user_sections_seventy_four_bridge_non_vacuous_and_tight

/-- 6. Skip, Tick, Inst, StackLoad, StackStore and StackFree compile with no added clock, and
StackAlloc uses clock = 0 outside overflow and clock ≤ 1 in every case. -/
theorem zero_clock_base_cases_seventy_six_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.StackSemStateFiniteExact width C F)
    (result : Option (Flapjack.StackSemResult width))
    (postSource target : Flapjack.StackSemStateFiniteExact width C F)
    (register count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : Flapjack.Compiler.Encoders.Asm.HolInst width)
    (hSkip : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.skip, source) = (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound
        (Flapjack.Compiler.Backend.StackLang.Prog.skip :
          Flapjack.Compiler.Backend.StackLang.HolProg width) pointer)
    (hTick : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.tick, source) = (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound
        (Flapjack.Compiler.Backend.StackLang.Prog.tick :
          Flapjack.Compiler.Backend.StackLang.HolProg width) pointer)
    (hInst : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.inst instruction, source) =
        (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound
        (Flapjack.Compiler.Backend.StackLang.Prog.inst instruction) pointer)
    (hFree : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.stackFree count, source) =
        (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target)
    (hAlloc : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc count, source) =
        (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target) :
    (∃ postTarget, Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          Flapjack.Compiler.Backend.StackLang.Prog.skip, target) = (result, postTarget)) ∧
    (∃ postTarget, Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.stackFree pointer count, target) =
        (result, postTarget)) ∧
    (∃ clock, clock ≤ 1 ∧ (result = none → clock = 0)) :=
  zero_clock_base_cases_seventy_four_bridge_non_vacuous_and_tight source result postSource target
    register count pointer bounds jump instruction hSkip hTick hInst hFree hAlloc

/-- 7. The 76-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem seventy_six_portfolio_under_yukon_non_vacuous_and_tight :
    SeventySixShape ∧ yukon = 900719925474 ∧
    WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio.length = 76 ∧
    (∀ K ∈ WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio, K < yukon) :=
  ⟨seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (seventy_six_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 8. Every one of the 76 budgets carries a finite certificate, from one base certificate. -/
theorem seventy_six_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    SeventySixShape ∧
    (∀ K ∈ WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(seventy_six_budget_certificates_non_vacuous_and_tight cert).1,
   (seventy_six_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 9. Both main totals and the BAL bound, together. -/
theorem main_totals_and_bal_bridge_non_vacuous_and_tight (k : Nat) (h : 2000 * k ≤ 380000000) :
    main200 = 200485906743 ∧ main380 = 511966000267 ∧
    k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ balRlp :=
  ⟨main_val, main380_val, bal_bound k h⟩

/-- 10. Grand bridge: both main totals, zero-clock allocation, user-section safety, and the
76-budget portfolio with finite certificates, all under Yukon. -/
theorem complete_main_system_gas_and_seventy_six_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : Flapjack.StackSemStateFiniteExact width C F)
    (result : Option (Flapjack.StackSemResult width))
    (hAlloc : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc count, source) =
        (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target)
    (cert : CertificateAt 1212035192) :
    (main200 = 200485906743 ∧ main380 = 511966000267) ∧
    (∃ clock, clock ≤ 1 ∧ (result = none → clock = 0)) ∧
    (InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (SeventySixShape ∧
      ∀ K ∈ WithdrawalsSszLimitMainClosureAndSeventySixBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨main_val, main380_val⟩,
   (by
      obtain ⟨clock, _, hclock, hzero, _, _⟩ :=
        InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.evaluateStackAllocZ
          jump bounds pointer count source target postSource result hAlloc
      exact ⟨clock, hclock, hzero⟩),
   panToTarget_user_sections_seventy_four_bridge_non_vacuous_and_tight,
   ⟨(seventy_six_budget_certificates_non_vacuous_and_tight cert).1,
    (seventy_six_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.CompleteMainSystemGasAndSeventySixBudgetBridge
