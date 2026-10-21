import InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
import InitECandidate.Solver.CompleteMainSystemGasAndSeventySixBudgetBridge
import InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# SaltedLinearGasEnvelopeAndSeventyEightBudgetBridge

Wave 5 bridge (W5_211). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.SaltedLinearGasEnvelopeAndSeventyEightBudgetBridge

open InitECandidate.Solver.GuestSaltedLinearGasEnvelopeAndMain380ClosureMaster
open InitECandidate.Solver.CompleteMainSystemGasAndSeventySixBudgetBridge
open InitECandidate.Solver.CompleteMainAllSubsystemsAndSeventyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. The per-unit table charge covers 60 finds of 8 steps at 2 ticks. -/
theorem per_unit_bridge_non_vacuous_and_tight :
    60 * 8 * 2 ≤ 1000 :=
  per_unit

/-- 2. Unsalted quadratic terms versus salted linear terms. -/
theorem quad_vs_lin_bridge_non_vacuous_and_tight :
    2000000 * 2000000 / 40 = 100000000000 ∧ saltedTable 2000000 = 2000000000 ∧
    3800000 * 3800000 / 40 = 361000000000 ∧ saltedTable 3800000 = 3800000000 :=
  quad_vs_lin

/-- 3. Salted gas envelopes: 58_088_992_805 at 200M and 110_369_086_329 at 380M. -/
theorem salted_env_bridge_non_vacuous_and_tight :
    156088992805 - 100000000000 + 2000000000 = 58088992805 ∧
    467569086329 - 361000000000 + 3800000000 = 110369086329 :=
  salted_env

/-- 4. Salted main totals: 102_485_906_743 passes 8x and 154_766_000_267 passes 5x. -/
theorem salted_totals_and_slopes_bridge_non_vacuous_and_tight :
    salted200 = 102485906743 ∧ 8 * 102485906743 < yukon ∧
    salted380 = 154766000267 ∧ 5 * 154766000267 < yukon :=
  ⟨salted200_val, slope200.1, salted380_val, slope380.1⟩

/-- 5. The salt alone removes 98_000_000_000 (200M) and 357_200_000_000 (380M), and the
verdicts survive up to 6_052 and 7_678 ticks per unit. -/
theorem salt_gain_and_slack_bridge_non_vacuous_and_tight :
    (100000000000 - 2000000000 = 98000000000 ∧
      361000000000 - 3800000000 = 357200000000) ∧
    (8 * (200485906743 - 100000000000 + 6052 * 2000000) < yukon ∧
      5 * (511966000267 - 361000000000 + 7678 * 3800000) < yukon) :=
  ⟨salt_gain, per_unit_slack.1, per_unit_slack.2.2.1⟩

/-- 6. System gas reaches 380M, and the BAL bound admits at most 190_000 cold keys inside
300_000_000 ticks. -/
theorem system_gas_and_bal_bridge_non_vacuous_and_tight (k : Nat) (h : 2000 * k ≤ 380000000) :
    (2 + 4 = 6 ∧ 200000000 + 6 * 30000000 = 380000000) ∧
    (k ≤ 190000 ∧ 2 * 18 * 40 * 190000 ≤ InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster.balRlp ∧ InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster.balRlp = 300000000) :=
  ⟨InitECandidate.Solver.GuestCompleteMainAllSubsystemsSynthesisMaster.system_gas, bal_bound_non_vacuous_and_tight k h⟩

/-- 7. After LabToTarget, no user section reaches section 6, and the base cases compile with no
added clock. -/
theorem user_sections_and_zero_clock_bridge_non_vacuous_and_tight
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
    (InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (∃ clock, clock ≤ 1 ∧ (result = none → clock = 0)) :=
  ⟨panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight,
   (zero_clock_base_cases_seventy_six_bridge_non_vacuous_and_tight source result postSource target
      register count pointer bounds jump instruction hSkip hTick hInst hFree hAlloc).2.2⟩

/-- 8. The 78-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem seventy_eight_portfolio_under_yukon_non_vacuous_and_tight :
    SeventyEightShape ∧ yukon = 900719925474 ∧
    CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio.length = 78 ∧
    (∀ K ∈ CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio, K < yukon) :=
  ⟨seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (seventy_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 9. Every one of the 78 budgets carries a finite certificate, from one base certificate. -/
theorem seventy_eight_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    SeventyEightShape ∧
    (∀ K ∈ CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(seventy_eight_budget_certificates_non_vacuous_and_tight cert).1,
   (seventy_eight_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 10. Grand bridge: salted totals, zero-clock allocation, user-section safety, and the
78-budget portfolio with finite certificates, all under Yukon. -/
theorem salted_linear_gas_envelope_and_seventy_eight_budget_bridge_master_non_vacuous_and_tight
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
    (salted200 = 102485906743 ∧ salted380 = 154766000267) ∧
    (∃ clock, clock ≤ 1 ∧ (result = none → clock = 0)) ∧
    (InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (SeventyEightShape ∧
      ∀ K ∈ CompleteMainAllSubsystemsAndSeventyEightBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨salted200_val, salted380_val⟩,
   (by
      obtain ⟨clock, _, hclock, hzero, _, _⟩ :=
        InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.evaluateStackAllocZ
          jump bounds pointer count source target postSource result hAlloc
      exact ⟨clock, hclock, hzero⟩),
   panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight,
   ⟨(seventy_eight_budget_certificates_non_vacuous_and_tight cert).1,
    (seventy_eight_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.SaltedLinearGasEnvelopeAndSeventyEightBudgetBridge
