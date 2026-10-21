import InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
import InitECandidate.Solver.StackRemoveBaseCasesZeroClockAndSixtyFourBudgetBridge
import InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# StackRemoveZeroClockPrologueSecp256k1AndSixtyEightBudgetBridge

Wave 5 bridge (W5_186). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.StackRemoveZeroClockPrologueSecp256k1AndSixtyEightBudgetBridge

open InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
open InitECandidate.Solver.StackRemoveBaseCasesZeroClockAndSixtyFourBudgetBridge
open InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Skip, Tick and Inst compile with no added clock. -/
theorem skip_tick_inst_zero_clock_bridge_non_vacuous_and_tight
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
  base_cases_zero_clock_non_vacuous_and_tight source result postSource target pointer bounds jump
    instruction hSkip hTick hInst

/-- 2. StackLoad and StackStore compile with no added clock. -/
theorem stack_load_store_zero_clock_bridge_non_vacuous_and_tight
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
  stack_load_store_zero_clock_non_vacuous_and_tight source result postSource target register count
    pointer bounds jump hLoad hStore

/-- 3. StackFree compiles with no added clock, and StackAlloc uses clock = 0 outside overflow
and clock ≤ 1 in every case. -/
theorem stack_free_and_alloc_zero_clock_bridge_non_vacuous_and_tight
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
  ⟨(stack_free_and_alloc_clock_non_vacuous_and_tight jump bounds pointer count source target
      postSource result hFree hAlloc).1,
   (by
      obtain ⟨clock, _, hclock, hzero, _, _⟩ :=
        InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.evaluateStackAllocZ
          jump bounds pointer count source target postSource result hAlloc
      exact ⟨clock, hclock, hzero⟩)⟩

/-- 4. Post-EVM balance: secp256k1_recover, two indexed tries and logs_bloom cost
4_859_866_650 ticks. -/
theorem post_evm_balance_non_vacuous_and_tight :
    postTerms = 4859866650 ∧
    500040000 + 4333160000 + 26666650 = 4859866650 ∧
    (∀ t : Nat, t ≤ 16668 → 30000 * t ≤ 500040000) ∧
    (∀ t : Nat, t ≤ 16666 → 2 * 130000 * t ≤ 4333160000) :=
  ⟨post_val, by decide, secp_total, tries_total⟩

/-- 5. Block totals with the post-EVM terms: 229_226_116_343 on the heap model and
199_895_347_399 with DAG memoization. -/
theorem block_totals_with_post_evm_non_vacuous_and_tight :
    224985309693 + postTerms = 229845176343 ∧
    195654540749 + postTerms = 200514407399 :=
  ⟨by have := InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster.sub_vals.1
      unfold postTerms; omega,
   by have := InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster.sub_vals.2
      unfold postTerms; omega⟩

/-- 6. ts+64 thresholds at 1x once the post-EVM terms are paid: L ≤ 38_574 on the heap model
and L ≤ 40_041 on the memoized model. -/
theorem lmax_one_times_with_post_evm_non_vacuous_and_tight :
    (∀ L : Nat,
      224985309693 +
          postTerms + 20000000 * L < yukon ↔ L ≤ 33543) ∧
    (∀ L : Nat,
      195654540749 +
          postTerms + 20000000 * L < yukon ↔ L ≤ 35010) := by
  constructor <;> intro L <;> unfold yukon postTerms <;> omega

/-- 7. At 4x with DAG memoization the threshold is L ≤ 6_264. -/
theorem lmax_four_times_memo_with_post_evm_non_vacuous_and_tight :
    (∀ L : Nat,
      4 * (195654540749 +
            postTerms + 20000000 * L) < yukon ↔ L ≤ 1233) ∧
    4 * (195654540749 +
          postTerms + 20000000 * 1233) < yukon ∧
    yukon ≤ 4 * (195654540749 +
          postTerms + 20000000 * 1234) := by
  refine ⟨?_, by decide, by decide⟩
  intro L
  unfold yukon postTerms
  omega

/-- 8. The 68-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem sixty_eight_portfolio_under_yukon_non_vacuous_and_tight :
    SixtyEightShape ∧ yukon = 900719925474 ∧
    portfolio.length = 68 ∧ (∀ K ∈ portfolio, K < yukon) :=
  ⟨sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, rfl,
   sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.1,
   fun K hK =>
     (sixty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2⟩

/-- 9. Every one of the 68 budgets carries a finite certificate, from one base certificate. -/
theorem sixty_eight_certificates_bridge_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    SixtyEightShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(sixty_eight_budget_certificates_non_vacuous_and_tight cert).1,
   (sixty_eight_budget_certificates_non_vacuous_and_tight cert).2.2⟩

/-- 10. Grand bridge: zero-clock allocation, post-EVM balance, both block totals, both
thresholds, and the 68-budget portfolio under Yukon. -/
theorem stack_remove_zero_clock_prologue_secp256k1_and_sixty_eight_budget_bridge_master_non_vacuous_and_tight
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
    postTerms = 4859866650 ∧
    (224985309693 +
        postTerms = 229845176343 ∧
      195654540749 +
        postTerms = 200514407399) ∧
    ((∀ L : Nat,
        224985309693 +
            postTerms + 20000000 * L < yukon ↔ L ≤ 33543) ∧
      (∀ L : Nat,
        4 * (195654540749 +
              postTerms + 20000000 * L) < yukon ↔ L ≤ 1233)) ∧
    (SixtyEightShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(by
      obtain ⟨clock, _, hclock, hzero, _, _⟩ :=
        InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.evaluateStackAllocZ
          jump bounds pointer count source target postSource result hAlloc
      exact ⟨clock, hclock, hzero⟩),
   post_val,
   ⟨block_totals_with_post_evm_non_vacuous_and_tight.1,
    block_totals_with_post_evm_non_vacuous_and_tight.2⟩,
   ⟨lmax_one_times_with_post_evm_non_vacuous_and_tight.1,
    lmax_four_times_memo_with_post_evm_non_vacuous_and_tight.1⟩,
   ⟨(sixty_eight_budget_certificates_non_vacuous_and_tight cert).1,
    (sixty_eight_budget_certificates_non_vacuous_and_tight cert).2.2⟩⟩

end InitECandidate.Solver.StackRemoveZeroClockPrologueSecp256k1AndSixtyEightBudgetBridge
