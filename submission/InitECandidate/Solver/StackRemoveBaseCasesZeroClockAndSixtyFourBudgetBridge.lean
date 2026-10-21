import InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock
import InitECandidate.Solver.ExactTicksNoLocValue6AndSixtyTwoBudgetBridge
import InitECandidate.Solver.FullBlockTransientProbesAndSixtyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# StackRemoveBaseCasesZeroClockAndSixtyFourBudgetBridge

Wave 5 bridge (W5_176). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.StackRemoveBaseCasesZeroClockAndSixtyFourBudgetBridge

open _root_.InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock
open InitECandidate.Solver.ExactTicksNoLocValue6AndSixtyTwoBudgetBridge
open InitECandidate.Solver.FullBlockTransientProbesAndSixtyFourBudgetMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Skip, Tick and Inst compile with no added clock. -/
theorem base_cases_zero_clock_non_vacuous_and_tight
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
        (Flapjack.Compiler.Backend.StackLang.Prog.skip : Flapjack.Compiler.Backend.StackLang.HolProg width) pointer)
    (hTick : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.tick, source) = (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound
        (Flapjack.Compiler.Backend.StackLang.Prog.tick : Flapjack.Compiler.Backend.StackLang.HolProg width) pointer)
    (hInst : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.inst instruction, source) = (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound
        (Flapjack.Compiler.Backend.StackLang.Prog.inst instruction) pointer) :
    (∃ postTarget,
      Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          Flapjack.Compiler.Backend.StackLang.Prog.skip, target) = (result, postTarget)) ∧
    (∃ postTarget,
      Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          Flapjack.Compiler.Backend.StackLang.Prog.tick, target) = (result, postTarget)) ∧
    (∃ postTarget,
      Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          (Flapjack.Compiler.Backend.StackLang.Prog.inst instruction), target) =
        (result, postTarget)) :=
  ⟨(by
      obtain ⟨postTarget, run, _⟩ := compCorrectSkipZ source result postSource target pointer
        bounds jump hSkip
      exact ⟨postTarget, run⟩),
   (by
      obtain ⟨postTarget, run, _⟩ := compCorrectTickZ source result postSource target pointer
        bounds jump hTick
      exact ⟨postTarget, run⟩),
   (by
      obtain ⟨postTarget, run, _⟩ := compCorrectInstZ source result postSource target pointer
        bounds jump instruction hInst
      exact ⟨postTarget, run⟩)⟩

/-- 2. StackLoad and StackStore compile to a target run with the source result. -/
theorem stack_load_store_zero_clock_non_vacuous_and_tight
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
        (Flapjack.Compiler.Backend.StackLang.Prog.stackLoad register count : Flapjack.Compiler.Backend.StackLang.HolProg width)
        pointer)
    (hStore : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.stackStore register count, source) =
        (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound
        (Flapjack.Compiler.Backend.StackLang.Prog.stackStore register count : Flapjack.Compiler.Backend.StackLang.HolProg width)
        pointer) :
    (∃ postTarget,
      Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          (Flapjack.Compiler.Backend.StackLang.Prog.stackLoad register count), target) =
        (result, postTarget)) ∧
    (∃ postTarget,
      Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer
          (Flapjack.Compiler.Backend.StackLang.Prog.stackStore register count), target) =
        (result, postTarget)) :=
  ⟨(by
      obtain ⟨postTarget, run, _⟩ := compCorrectStackLoadZ source result postSource target
        register count pointer bounds jump hLoad
      exact ⟨postTarget, run⟩),
   (by
      obtain ⟨postTarget, run, _⟩ := compCorrectStackStoreZ source result postSource target
        register count pointer bounds jump hStore
      exact ⟨postTarget, run⟩)⟩

/-- 3. StackFree compiles with no added clock, and StackAlloc uses clock = 0 outside overflow
and clock ≤ 1 in every case. -/
theorem stack_free_and_alloc_clock_non_vacuous_and_tight
    {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : Flapjack.StackSemStateFiniteExact width C F)
    (result : Option (Flapjack.StackSemResult width))
    (hFree : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.stackFree count, source) = (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target)
    (hAlloc : Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackLang.Prog.stackAlloc count, source) =
        (result, postSource) ∧
      result ≠ some Flapjack.StackSemResult.error ∧
      Flapjack.Compiler.Backend.StackRemove.stateRelHOL jump bounds pointer source target) :
    (∃ postTarget,
      Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.stackFree pointer count, target) = (result, postTarget)) ∧
    (∃ clock postTarget, clock ≤ 1 ∧ (result = none → clock = 0) ∧
      Flapjack.StackSemEvaluate.evaluate
        (Flapjack.Compiler.Backend.StackRemove.stackAlloc jump pointer count,
          {target with clock := clock + target.clock}) = (result, postTarget)) :=
  ⟨(by
      obtain ⟨postTarget, run, _⟩ := evaluateStackFreeZ jump bounds pointer count source target
        postSource result hFree
      exact ⟨postTarget, run⟩),
   (by
      obtain ⟨clock, postTarget, hclock, hzero, run, _⟩ := evaluateStackAllocZ jump bounds pointer
        count source target postSource result hAlloc
      exact ⟨clock, postTarget, hclock, hzero, run⟩)⟩

/-- 4. Exact per-node decode ticks: leaf 43, extension 48, branch 326. -/
theorem exact_ticks_sixty_four_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tLeaf = 43 ∧
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tExt = 48 ∧
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tBranch = 326 :=
  exact_ticks_per_node_bridge_non_vacuous_and_tight

/-- 5. Decode ticks stay under 31_092_374_808 for any heap-fitting node set. -/
theorem ticks_le_heap_sixty_four_bridge_non_vacuous_and_tight (L E B : Nat)
    (h : InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf L E B ≤
      InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapAvail) :
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.decodeTicks L E B ≤
      31092374808 :=
  ExactTicksNoLocValue6AndSixtyTwoBudgetBridge.ticks_le_heap_bridge_non_vacuous_and_tight L E B h

/-- 6. Memoized DAG decode is exactly 10_938_743_528 ticks. -/
theorem decode_memo_sixty_four_bridge_non_vacuous_and_tight (L E B n : Nat)
    (hn : 4 * n ≤ 134217712) (h : L + E + B ≤ n) :
    326 * 33554428 = 10938743528 ∧
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.decodeTicks L E B ≤
      10938743528 :=
  ⟨(decode_memo_val_bridge_non_vacuous_and_tight L E B n hn h).2,
   (decode_memo_val_bridge_non_vacuous_and_tight L E B n hn h).2 ▸
     (decode_memo_val_bridge_non_vacuous_and_tight L E B n hn h).1⟩

/-- 7. Resolve-step subtotals at r = 8: 224_985_309_693 and 195_654_540_749. -/
theorem resolve_step_subtotals_sixty_four_bridge_non_vacuous_and_tight :
    InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster.subHeap =
      224985309693 ∧
    InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster.subMemo =
      195654540749 :=
  ⟨resolve_step_subtotals_at_eight_non_vacuous_and_tight.1,
   resolve_step_subtotals_at_eight_non_vacuous_and_tight.2.1⟩

/-- 8. The 64-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem sixty_four_portfolio_under_yukon_non_vacuous_and_tight :
    SixtyFourShape ∧ ClaimPayloads ∧ yukon = 900719925474 :=
  ⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight, rfl⟩

/-- 9. Every one of the 64 budgets carries a finite certificate, from one base certificate. -/
theorem sixty_four_certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    SixtyFourShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(certificates_non_vacuous_and_tight cert).1,
   (certificates_non_vacuous_and_tight cert).2.2⟩

/-- 10. Grand bridge: zero-clock allocation, exact decode ticks, resolve-step subtotals,
and the 64-budget portfolio under Yukon. -/
theorem stack_remove_base_cases_zero_clock_and_sixty_four_budget_bridge_master_non_vacuous_and_tight
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
    (InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tLeaf = 43 ∧
      InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tExt = 48 ∧
      InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.tBranch = 326 ∧
      326 * 33554428 = 10938743528) ∧
    (InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster.subHeap =
        224985309693 ∧
      InitECandidate.Solver.GuestFullBlockWithTransientStorageAndProbesMaster.subMemo =
        195654540749) ∧
    (SixtyFourShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨(by
      obtain ⟨clock, _, hclock, hzero, _, _⟩ := evaluateStackAllocZ jump bounds pointer count
        source target postSource result hAlloc
      exact ⟨clock, hclock, hzero⟩),
   ⟨exact_ticks_per_node_bridge_non_vacuous_and_tight.1,
    exact_ticks_per_node_bridge_non_vacuous_and_tight.2.1,
    exact_ticks_per_node_bridge_non_vacuous_and_tight.2.2,
    InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit.decode_memo_val.1⟩,
   ⟨resolve_step_subtotals_at_eight_non_vacuous_and_tight.1,
    resolve_step_subtotals_at_eight_non_vacuous_and_tight.2.1⟩,
   ⟨(certificates_non_vacuous_and_tight cert).1,
    (certificates_non_vacuous_and_tight cert).2.2⟩⟩

end InitECandidate.Solver.StackRemoveBaseCasesZeroClockAndSixtyFourBudgetBridge
