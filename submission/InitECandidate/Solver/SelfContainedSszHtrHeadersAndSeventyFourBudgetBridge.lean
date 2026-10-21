import InitECandidate.Solver.WithdrawalsSszLimitAndSeventyTwoBudgetBridge
import InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyBudgetMaster
import InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# SelfContainedSszHtrHeadersAndSeventyFourBudgetBridge

Wave 5 bridge (W5_201). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyFourBudgetBridge

open InitECandidate.Solver.WithdrawalsSszLimitAndSeventyTwoBudgetBridge
open InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyBudgetMaster
open InitECandidate.Solver.SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. The SSZ limit is not the spec cap: InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.nwdMax passes ssz_fixed_list_count. -/
theorem ssz_no_cap_seventy_four_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.nwdMax ≤ 9223372036854775807 ∧ 16 < InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.nwdMax :=
  ssz_no_cap_bridge_non_vacuous_and_tight

/-- 2. At 1x with salt the withdrawal phase closes, margin 626_933_565_707. -/
theorem close_1x_salted_seventy_four_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 0 InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.nwdMax ≤ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r1 ∧ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r1 - InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 0 InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.nwdMax = 626933565707 :=
  close_1x_salted_bridge_non_vacuous_and_tight

/-- 3. Unsalted thresholds: n ≤ 323_652 at f = 6 and n ≤ 281_528 at f = 8. -/
theorem unsalted_thresholds_seventy_four_bridge_non_vacuous_and_tight :
    (InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 6 323652 ≤ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r1 ∧ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r1 < InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 6 323653) ∧
    (InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 8 281528 ≤ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r1 ∧ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r1 < InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 8 281529) :=
  unsalted_thresholds_bridge_non_vacuous_and_tight

/-- 4. At 4x the salted linear threshold is n ≤ 189_516. -/
theorem nmax_4x_seventy_four_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 0 189516 ≤ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r4 ∧ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r4 < InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 0 189517 :=
  nmax_4x_bridge_non_vacuous_and_tight

/-- 5. Under the spec cap n ≤ 16 the phase closes at 4x even unsalted with f = 8,
margin 25_014_084_625. -/
theorem spec_cap_closes_seventy_four_bridge_non_vacuous_and_tight (n : Nat) (h : n ≤ 16) :
    InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 8 n ≤ InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 8 16 ∧ InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 8 16 ≤ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r4 ∧ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r4 - InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 8 16 = 25014084625 :=
  spec_cap_closes_bridge_non_vacuous_and_tight n h

/-- 6. Skip, Tick, Inst, StackLoad, StackStore and StackFree compile with no added clock, and
StackAlloc uses clock = 0 outside overflow and clock ≤ 1 in every case. -/
theorem zero_clock_base_cases_seventy_four_bridge_non_vacuous_and_tight
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
  zero_clock_base_cases_bridge_non_vacuous_and_tight source result postSource target register count
    pointer bounds jump instruction hSkip hTick hInst hFree hAlloc

/-- 7. After LabToTarget, no user section reaches section 6 by jump, conditional jump, call or
locValue. -/
theorem panToTarget_user_sections_seventy_four_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  panToTarget_user_sections_seventy_two_bridge_non_vacuous_and_tight

/-- 8. The 74-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem seventy_four_portfolio_under_yukon_non_vacuous_and_tight :
    SeventyFourShape ∧ yukon = 900719925474 ∧
    SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.portfolio.length = 74 ∧
    (∀ K ∈ SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.portfolio, K < yukon) :=
  ⟨seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (seventy_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 9. Every one of the 74 budgets carries a finite certificate, from one base certificate. -/
theorem seventy_four_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    SeventyFourShape ∧
    (∀ K ∈ SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(seventy_four_budget_certificates_non_vacuous_and_tight cert).1,
   (seventy_four_budget_certificates_non_vacuous_and_tight cert).2⟩

/-- 10. Grand bridge: spec-cap closure, zero-clock allocation, user-section safety, and the
74-budget portfolio with finite certificates, all under Yukon. -/
theorem self_contained_ssz_htr_headers_and_seventy_four_budget_bridge_master_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : Flapjack.StackSemStateFiniteExact width C F)
    (result : Option (Flapjack.StackSemResult width))
    (hAlloc : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc count, source) =
        (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target)
    (n : Nat) (hn : n ≤ 16)
    (cert : CertificateAt 1212035192) :
    (InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.nwdMax ≤ 9223372036854775807 ∧ 16 < InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.nwdMax) ∧
    (InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 8 n ≤ InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 8 16 ∧ InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound.r4 - InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit.wdTicks 8 16 = 25014084625) ∧
    (∃ clock, clock ≤ 1 ∧ (result = none → clock = 0)) ∧
    (InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (SeventyFourShape ∧
      ∀ K ∈ SszHtrHeadersWithdrawalsAndSeventyFourBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨ssz_no_cap_bridge_non_vacuous_and_tight,
   ⟨(spec_cap_closes_bridge_non_vacuous_and_tight n hn).1,
    (spec_cap_closes_bridge_non_vacuous_and_tight n hn).2.2⟩,
   (by
      obtain ⟨clock, _, hclock, hzero, _, _⟩ :=
        InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.evaluateStackAllocZ
          jump bounds pointer count source target postSource result hAlloc
      exact ⟨clock, hclock, hzero⟩),
   panToTarget_user_sections_seventy_two_bridge_non_vacuous_and_tight,
   ⟨(seventy_four_budget_certificates_non_vacuous_and_tight cert).1,
    (seventy_four_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.SelfContainedSszHtrHeadersAndSeventyFourBudgetBridge
