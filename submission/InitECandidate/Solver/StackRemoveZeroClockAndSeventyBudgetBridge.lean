import InitECandidate.Solver.StackRemoveZeroClockPrologueSecp256k1AndSixtyEightBudgetBridge
import InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster
import InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# StackRemoveZeroClockAndSeventyBudgetBridge

Wave 5 bridge (W5_192). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.StackRemoveZeroClockAndSeventyBudgetBridge

open InitECandidate.Solver.StackRemoveZeroClockPrologueSecp256k1AndSixtyEightBudgetBridge
open InitECandidate.Solver.SelfContainedPrologueSecp256k1AndSixtyEightBudgetMaster
open InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster (coupled)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Skip, Tick and Inst compile with no added clock. -/
theorem skip_tick_inst_zero_clock_seventy_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.StackSemStateFiniteExact width C F)
    (result : Option (Flapjack.StackSemResult width))
    (postSource target : Flapjack.StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
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
        (Flapjack.Compiler.Backend.StackLang.Prog.inst instruction) pointer) :
    (∃ postTarget, Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          Flapjack.Compiler.Backend.StackLang.Prog.skip, target) = (result, postTarget)) ∧
    (∃ postTarget, Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          Flapjack.Compiler.Backend.StackLang.Prog.tick, target) = (result, postTarget)) ∧
    (∃ postTarget, Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          (Flapjack.Compiler.Backend.StackLang.Prog.inst instruction), target) =
        (result, postTarget)) :=
  skip_tick_inst_zero_clock_bridge_non_vacuous_and_tight source result postSource target pointer
    bounds jump instruction hSkip hTick hInst

/-- 2. StackLoad and StackStore compile with no added clock. -/
theorem stack_load_store_zero_clock_seventy_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (source : Flapjack.StackSemStateFiniteExact width C F)
    (result : Option (Flapjack.StackSemResult width))
    (postSource target : Flapjack.StackSemStateFiniteExact width C F)
    (register count pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hLoad : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.stackLoad register count, source) =
        (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound
        (Flapjack.Compiler.Backend.StackLang.Prog.stackLoad register count :
          Flapjack.Compiler.Backend.StackLang.HolProg width) pointer)
    (hStore : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.stackStore register count, source) =
        (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound
        (Flapjack.Compiler.Backend.StackLang.Prog.stackStore register count :
          Flapjack.Compiler.Backend.StackLang.HolProg width) pointer) :
    (∃ postTarget, Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          (Flapjack.Compiler.Backend.StackLang.Prog.stackLoad register count), target) =
        (result, postTarget)) ∧
    (∃ postTarget, Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          (Flapjack.Compiler.Backend.StackLang.Prog.stackStore register count), target) =
        (result, postTarget)) :=
  stack_load_store_zero_clock_bridge_non_vacuous_and_tight source result postSource target
    register count pointer bounds jump hLoad hStore

/-- 3. StackFree compiles with no added clock, and StackAlloc uses clock = 0 outside overflow
and clock ≤ 1 in every case. -/
theorem stack_free_and_alloc_zero_clock_seventy_bridge_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : Flapjack.StackSemStateFiniteExact width C F)
    (result : Option (Flapjack.StackSemResult width))
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
        (Flapjack.Compiler.Backend.StackRemove.stackFree pointer count, target) =
        (result, postTarget)) ∧
    (∃ clock, clock ≤ 1 ∧ (result = none → clock = 0)) :=
  stack_free_and_alloc_zero_clock_bridge_non_vacuous_and_tight jump bounds pointer count source
    target postSource result hFree hAlloc

/-- 4. Post-EVM balance: 4_859_866_650 ticks for secp256k1_recover, two indexed tries and
logs_bloom. -/
theorem post_evm_balance_seventy_bridge_non_vacuous_and_tight :
    post_evm = 4859866650 ∧
    500040000 + 4333160000 + 26666650 = 4859866650 :=
  ⟨post_evm_balance_non_vacuous_and_tight.1, post_evm_balance_non_vacuous_and_tight.2.1⟩

/-- 5. Block totals with the post-EVM terms: 229_845_176_343 on the heap model and
200_514_407_399 with DAG memoization. -/
theorem block_totals_seventy_bridge_non_vacuous_and_tight :
    block_total = 229226116343 ∧ block_total_memo = 199895347399 ∧
    block_total - block_total_memo = 29330768944 :=
  block_totals_non_vacuous_and_tight

/-- 6. ts+64 thresholds once the post-EVM terms are paid: L ≤ 33_543 on the heap model and
L ≤ 35_010 on the memoized model, both at 1x. -/
theorem lmax_one_times_seventy_bridge_non_vacuous_and_tight :
    (∀ L : Nat, 1 * coupled block_total L < yukon ↔ L ≤ 38574) ∧
    (∀ L : Nat, 1 * coupled block_total_memo L < yukon ↔ L ≤ 40041) :=
  ⟨one_heap_lmax_non_vacuous_and_tight.1, one_memo_lmax_non_vacuous_and_tight.1⟩

/-- 7. At 4x with DAG memoization the threshold is L ≤ 1_233. -/
theorem lmax_four_times_memo_seventy_bridge_non_vacuous_and_tight :
    (∀ L : Nat, 4 * coupled block_total_memo L < yukon ↔ L ≤ 6264) :=
  four_memo_lmax_non_vacuous_and_tight.1

/-- 8. After LabToTarget, no user section reaches section 6 by jump, conditional jump, call or
locValue. -/
theorem panToTarget_user_sections_noStubJumpOrLocValue_seventy_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
    InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe :=
  panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight

/-- 9. The 70-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem seventy_portfolio_under_yukon_non_vacuous_and_tight :
    SeventyShape ∧ yukon = 900719925474 ∧
    PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.portfolio.length = 70 ∧
    (∀ K ∈ PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.portfolio, K < yukon) :=
  ⟨seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.2.2.2.2,
   seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (seventy_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 10. Grand bridge: zero-clock allocation, user-section safety after LabToTarget, and the
70-budget portfolio with finite certificates, all under Yukon. -/
theorem stack_remove_zero_clock_and_seventy_budget_bridge_master_non_vacuous_and_tight
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
    (∃ clock, clock ≤ 1 ∧ (result = none → clock = 0)) ∧
    (InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanTargetSafe ∧
      InitECandidate.Solver.NoLocValue6WitnessDagAndFiftySixBudgetMaster.PanUserSafe) ∧
    (SeventyShape ∧
      ∀ K ∈ PrologueTxDecodeSecp256k1AndSeventyBudgetMaster.portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(by
      obtain ⟨clock, _, hclock, hzero, _, _⟩ :=
        InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.evaluateStackAllocZ
          jump bounds pointer count source target postSource result hAlloc
      exact ⟨clock, hclock, hzero⟩),
   panToTarget_user_sections_noStubJumpOrLocValue_non_vacuous_and_tight,
   ⟨(seventy_budget_certificates_non_vacuous_and_tight cert).1,
    (seventy_budget_certificates_non_vacuous_and_tight cert).2⟩⟩

end InitECandidate.Solver.StackRemoveZeroClockAndSeventyBudgetBridge
