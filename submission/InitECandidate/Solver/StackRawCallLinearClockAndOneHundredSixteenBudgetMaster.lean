import InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge
import InitECandidate.Solver.JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! The uncached jumpdest scans invalidate the previous global gas estimate for
the current Guest. The 110x/77x arithmetic explicitly assumes the proposed
per-code jumpdest cache and the previous model's remaining assumptions.
Finite semantic certificates remain conditional on the base certificate;
none is inferred from the arithmetic cost estimates. -/
namespace InitECandidate.Solver.StackRawCallLinearClockAndOneHundredSixteenBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

abbrev Previous := JumpdestDualLPOneHundredTenXAndOneHundredFourteenBudgetMaster.oneHundredFourteenExplicitBudgets

def oneHundredSixteenExplicitBudgets : List Nat := Previous ++ [900717000000, 900718000000]
abbrev portfolio := oneHundredSixteenExplicitBudgets

def OneHundredSixteenShape : Prop :=
  portfolio.length = 116 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 114 = Previous ∧
  portfolio.drop 114 = [900717000000, 900718000000] ∧
  portfolio.getLast? = some 900718000000 ∧ yukon = 900719925474

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Encoders.Asm
open _root_.InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall (rawCallSections)

theorem rawCall_linearClock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (nonError : result ≠ some .error) (relation : stateRel info source target) :
    ∃ extra targetPost stackSpace,
      extra + post.clock ≤ source.clock ∧ targetPost.clock = post.clock ∧
      stateRel info post targetPost ∧
      StackSemEvaluate.evaluate (comp info program, {target with clock := target.clock + extra}) =
        (result, {targetPost with stackSpace := stackSpace}) :=
  StackRawCallLinearClockAndZeroExtraBridge.rawCall_linearClock program source target post info result run nonError relation

theorem rawCall_extra_le_clock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (nonError : result ≠ some .error) (relation : stateRel info source target) :
    ∃ extra targetPost, extra ≤ source.clock ∧ target.clock + extra ≤ 2 * source.clock ∧
      StackSemEvaluate.evaluate (comp info program, {target with clock := target.clock + extra}) =
        (result, targetPost) :=
  StackRawCallLinearClockAndZeroExtraBridge.rawCall_extra_le_clock program source target post info result run nonError relation

theorem entrySimulationB_extra_le_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
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
  StackRawCallLinearClockAndZeroExtraBridge.entrySimulationB_extra_le code source start clock result post distinct sourceCode run nonError

theorem pancake_rawCall_stackAlloc_stackRemove_clock_non_vacuous_and_tight {width : Nat} [NeZero width] {C F : Type}
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
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
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
  StackRawCallLinearClockAndZeroExtraBridge.pancake_rawCall_stackAlloc_stackRemove_clock arch prog wc ac perf dc info

theorem call_val_non_vacuous_and_tight : callTicks = 67884 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.call_val

theorem uncached_slopes_non_vacuous_and_tight : mainUncached200 = 112163577490 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 209425139355 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.uncached_slopes

theorem cached_tight_non_vacuous_and_tight : costC 0 0 0 0 0 0 (inputBytes / 4) 2000000 = 6619898520 ∧
    costC 0 0 0 0 0 0 (inputBytes / 4) 3800000 = 9859898520 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached_tight

theorem cached_slopes_non_vacuous_and_tight : mainCached200 = 8145414250 ∧ 110 * mainCached200 < yukon ∧
    yukon < 111 * mainCached200 ∧ mainCached380 = 11669833258 ∧ 77 * mainCached380 < yukon ∧
    yukon < 78 * mainCached380 :=
  GuestExactSstoreCallLPAndJumpdestDualBoundMaster.cached_slopes

theorem one_hundred_sixteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight :
    OneHundredSixteenShape := by
  unfold OneHundredSixteenShape
  decide

theorem one_hundred_sixteen_budget_last_margin_non_vacuous_and_tight :
    oneHundredSixteenExplicitBudgets.length = 116 ∧
    oneHundredSixteenExplicitBudgets.getLast? = some 900718000000 ∧
    yukon - 900718000000 = 1925474 := by decide

theorem one_hundred_sixteen_budgets_under_yukon_non_vacuous_and_tight :
    oneHundredSixteenExplicitBudgets.Pairwise (· < ·) ∧
    (∀ K ∈ oneHundredSixteenExplicitBudgets, K < 900719925474) := by
  refine ⟨one_hundred_sixteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.1, ?_⟩
  intro K hK
  exact (one_hundred_sixteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).2

theorem one_hundred_sixteen_budget_certificates_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredSixteenShape ∧
    (∀ K ∈ oneHundredSixteenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨one_hundred_sixteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (one_hundred_sixteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight.2.2.1 K hK).1 cert

#print axioms rawCall_linearClock_non_vacuous_and_tight
#print axioms rawCall_extra_le_clock_non_vacuous_and_tight
#print axioms entrySimulationB_extra_le_non_vacuous_and_tight
#print axioms pancake_rawCall_stackAlloc_stackRemove_clock_non_vacuous_and_tight
#print axioms call_val_non_vacuous_and_tight
#print axioms uncached_slopes_non_vacuous_and_tight
#print axioms cached_tight_non_vacuous_and_tight
#print axioms cached_slopes_non_vacuous_and_tight
#print axioms one_hundred_sixteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight
#print axioms one_hundred_sixteen_budget_last_margin_non_vacuous_and_tight
#print axioms one_hundred_sixteen_budgets_under_yukon_non_vacuous_and_tight
#print axioms one_hundred_sixteen_budget_certificates_non_vacuous_and_tight

end InitECandidate.Solver.StackRawCallLinearClockAndOneHundredSixteenBudgetMaster
