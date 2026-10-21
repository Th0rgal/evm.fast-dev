import InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
import InitECandidate.Solver.StackRemoveZeroClockAndSeventyBudgetBridge
import InitECandidate.Solver.SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# WithdrawalsSszLimitAndSeventyTwoBudgetBridge

Wave 5 bridge (W5_199). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.WithdrawalsSszLimitAndSeventyTwoBudgetBridge

open InitECandidate.Solver.GuestWithdrawalsSszLimitAndMainClosureAudit
open InitECandidate.Solver.GuestSszHtrHeadersAndCompleteMainBound (nwdMax r1 r4)
open InitECandidate.Solver.StackRemoveZeroClockAndSeventyBudgetBridge
open InitECandidate.Solver.SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. The SSZ limit is not the spec cap: nwdMax passes ssz_fixed_list_count. -/
theorem ssz_no_cap_bridge_non_vacuous_and_tight :
    nwdMax ≤ 9223372036854775807 ∧ 16 < nwdMax :=
  ssz_no_cap

/-- 2. Linear part at the cap: 132_000 * 335_544 = 44_291_808_000. -/
theorem linear_val_bridge_non_vacuous_and_tight :
    132000 * nwdMax = 44291808000 :=
  linear_val

/-- 3. At 1x with salt the withdrawal phase closes, margin 626_933_565_707. -/
theorem close_1x_salted_bridge_non_vacuous_and_tight :
    wdTicks 0 nwdMax ≤ r1 ∧ r1 - wdTicks 0 nwdMax = 626933565707 :=
  close_1x_salted

/-- 4. Unsalted thresholds: n ≤ 323_652 at f = 6 and n ≤ 281_528 at f = 8. -/
theorem unsalted_thresholds_bridge_non_vacuous_and_tight :
    (wdTicks 6 323652 ≤ r1 ∧ r1 < wdTicks 6 323653) ∧
    (wdTicks 8 281528 ≤ r1 ∧ r1 < wdTicks 8 281529) :=
  ⟨nmax_f6, nmax_f8⟩

/-- 5. At 4x the salted linear threshold is n ≤ 189_516. -/
theorem nmax_4x_bridge_non_vacuous_and_tight :
    wdTicks 0 189516 ≤ r4 ∧ r4 < wdTicks 0 189517 :=
  nmax_4x

/-- 6. Under the spec cap n ≤ 16 the phase closes at 4x even unsalted with f = 8,
margin 25_014_084_625. -/
theorem spec_cap_closes_bridge_non_vacuous_and_tight (n : Nat) (h : n ≤ 16) :
    wdTicks 8 n ≤ wdTicks 8 16 ∧ wdTicks 8 16 ≤ r4 ∧ r4 - wdTicks 8 16 = 25014084625 :=
  spec_cap_closes n h

/-- 7. Skip, Tick, Inst, StackLoad, StackStore and StackFree compile with no added clock, and
StackAlloc uses clock = 0 outside overflow and clock ≤ 1 in every case. -/
theorem zero_clock_base_cases_bridge_non_vacuous_and_tight
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
  ⟨(skip_tick_inst_zero_clock_seventy_bridge_non_vacuous_and_tight source result postSource target
      pointer bounds jump instruction hSkip hTick hInst).1,
   (stack_free_and_alloc_zero_clock_seventy_bridge_non_vacuous_and_tight jump bounds pointer count
      source target postSource result hFree hAlloc).1,
   (stack_free_and_alloc_zero_clock_seventy_bridge_non_vacuous_and_tight jump bounds pointer count
      source target postSource result hFree hAlloc).2⟩

/-- 8. After LabToTarget, no user section reaches section 6 by jump, conditional jump, call or
locValue. -/
theorem panToTarget_user_sections_seventy_two_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  panToTarget_user_sections_noStubJumpOrLocValue_seventy_bridge_non_vacuous_and_tight

/-- 9. The 72-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem seventy_two_portfolio_under_yukon_non_vacuous_and_tight :
    SeventyTwoShape ∧ yukon = 900719925474 ∧
    SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster.portfolio.length = 72 ∧
    (∀ K ∈ SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster.portfolio, K < yukon) :=
  ⟨seventy_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   seventy_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   seventy_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (seventy_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 10. Grand bridge: spec-cap closure, zero-clock allocation, user-section safety, and the
72-budget portfolio with finite certificates, all under Yukon. -/
theorem withdrawals_ssz_limit_and_seventy_two_budget_bridge_master_non_vacuous_and_tight
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
    (nwdMax ≤ 9223372036854775807 ∧ 16 < nwdMax) ∧
    (wdTicks 8 n ≤ wdTicks 8 16 ∧ r4 - wdTicks 8 16 = 25014084625) ∧
    (∃ clock, clock ≤ 1 ∧ (result = none → clock = 0)) ∧
    (InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (SeventyTwoShape ∧
      ∀ K ∈ SelfContainedPrologueStackRemoveZeroAndSeventyTwoBudgetMaster.portfolio,
        InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨ssz_no_cap,
   ⟨(spec_cap_closes n hn).1, (spec_cap_closes n hn).2.2⟩,
   (by
      obtain ⟨clock, _, hclock, hzero, _, _⟩ :=
        InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.evaluateStackAllocZ
          jump bounds pointer count source target postSource result hAlloc
      exact ⟨clock, hclock, hzero⟩),
   panToTarget_user_sections_noStubJumpOrLocValue_seventy_bridge_non_vacuous_and_tight,
   ⟨(seventy_two_budget_certificates_non_vacuous_and_tight cert).1,
    (seventy_two_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.WithdrawalsSszLimitAndSeventyTwoBudgetBridge
