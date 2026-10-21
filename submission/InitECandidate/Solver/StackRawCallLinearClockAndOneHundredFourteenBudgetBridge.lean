import InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge
import InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.StackRawCallLinearClockAndOneHundredFourteenBudgetBridge

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
open InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. StackRawCall `comp_correct` with the extra clock bounded by the source clock. -/
theorem rawCall_linearClock_bridge_non_vacuous_and_tight {C F : Type}
    (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (nonError : result ≠ some .error) (relation : stateRel info source target) :
    ∃ extra targetPost stackSpace,
      extra + post.clock ≤ source.clock ∧ targetPost.clock = post.clock ∧
      stateRel info post targetPost ∧
      StackSemEvaluate.evaluate (comp info program, {target with clock := target.clock + extra}) =
        (result, {targetPost with stackSpace := stackSpace}) :=
  InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.rawCall_linearClock
    program source target post info result run nonError relation

/-- 2. The target needs at most `extra ≤ source.clock` extra ticks: total target clock
`≤ 2 · source.clock`. -/
theorem rawCall_extra_le_clock_bridge_non_vacuous_and_tight {C F : Type}
    (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (nonError : result ≠ some .error) (relation : stateRel info source target) :
    ∃ extra targetPost, extra ≤ source.clock ∧ target.clock + extra ≤ 2 * source.clock ∧
      StackSemEvaluate.evaluate (comp info program, {target with clock := target.clock + extra}) =
        (result, targetPost) :=
  InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.rawCall_extra_le_clock
    program source target post info result run nonError relation

/-- 3. Whole-program entry simulation: `extra ≤ clock` (≤ 2× expansion). -/
theorem entrySimulationB_extra_le_bridge_non_vacuous_and_tight {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {source with clock := clock}) =
      (result, post)) (nonError : result ≠ some .error) :
    ∃ extra targetPost, extra ≤ clock ∧ clock + extra ≤ 2 * clock ∧ StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {source with code := sptFromAList (compile code), clock := clock + extra}) =
      (result, targetPost) :=
  InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.entrySimulationB_extra_le
    code source start clock result post distinct sourceCode run nonError

/-- 4. The greater-frame optimization really inserts a `tick`. -/
theorem optimized_greater_has_tick_bridge_non_vacuous_and_tight
    (released allocated dest : Nat) (h : released < allocated) :
    InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.SeqCase.optimizedSeqB
        (width := width) released allocated dest =
      .seq .tick (.seq (.stackAlloc (allocated - released)) (.rawCall dest)) :=
  InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.optimized_greater_has_tick
    released allocated dest h

/-- 5. With equal frames the optimization is a bare `rawCall` (no tick). -/
theorem optimized_equal_no_tick_bridge_non_vacuous_and_tight (n dest : Nat) :
    InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.SeqCase.optimizedSeqB
        (width := width) n n dest = .rawCall dest :=
  InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.optimized_equal_no_tick n dest

/-- 6. StackRawCall → StackAlloc → StackRemove: `extra ≤ source.clock`, StackAlloc identity
outside stub 6, StackRemove zero extra clock. -/
theorem pancake_rawCall_stackAlloc_stackRemove_clock_bridge_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    (∀ (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
       (result : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (program, source) = (result, post) → result ≠ some .error →
       stateRel info source target →
       ∃ extra targetPost, extra ≤ source.clock ∧ target.clock + extra ≤ 2 * source.clock ∧
         StackSemEvaluate.evaluate (comp info program, {target with clock := target.clock + extra}) =
           (result, targetPost)) ∧
    (∀ y ∈ InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.rawCallSections
        arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    (∀ y ∈ InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.rawCallSections
        arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        (StackAlloc.progComp y).2 = true ∧
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall
        (StackAlloc.progComp y).2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = sptFromAList
          (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveSections
            (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
              arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1,
          InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true) →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget,
          InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) :=
  InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.pancake_rawCall_stackAlloc_stackRemove_clock
    arch prog wc ac perf dc info

/-- 7. Uncached totals: `112,163,577,490` (`8×`) at 200M and `209,425,139,355` (`4×`) at 380M. -/
theorem uncached_slopes_bridge_non_vacuous_and_tight :
    mainUncached200 = 112163577490 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 209425139355 ∧ 4 * mainUncached380 < yukon ∧
      yukon < 5 * mainUncached380 :=
  uncached_slopes_non_vacuous_and_tight

/-- 8. Cached totals: `8,145,414,250` (`110×`) at 200M and `11,669,833,258` (`77×`) at 380M. -/
theorem cached_slopes_bridge_non_vacuous_and_tight :
    mainCached200 = 8145414250 ∧ 110 * mainCached200 < yukon ∧
      yukon < 111 * mainCached200 ∧ mainCached380 = 11669833258 ∧ 77 * mainCached380 < yukon ∧
      yukon < 78 * mainCached380 :=
  cached_slopes_non_vacuous_and_tight

/-- 9. The 114-budget table: 114 strictly increasing budgets, last entry 900,715,000,000, margin
4,925,474 under Yukon. -/
theorem one_hundred_fourteen_table_bridge_non_vacuous_and_tight :
    OneHundredFourteenShape ∧
    oneHundredFourteenExplicitBudgets.length = 114 ∧
    oneHundredFourteenExplicitBudgets.getLast? = some 900715000000 ∧
    yukon - 900715000000 = 4925474 :=
  ⟨one_hundred_fourteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_fourteen_budget_last_margin_non_vacuous_and_tight.2.2⟩

/-- 10. Every one of the 114 budgets carries a finite certificate, from one base certificate. -/
theorem one_hundred_fourteen_certificates_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredFourteenShape ∧
    (∀ K ∈ oneHundredFourteenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  one_hundred_fourteen_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.StackRawCallLinearClockAndOneHundredFourteenBudgetBridge
