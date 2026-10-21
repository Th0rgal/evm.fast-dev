import InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
import InitECandidate.Solver.PanToStackNamesEndToEndLinearClockMaster
import InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.SstoreDirtyKeyGasOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetBridge

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
open InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. A dirty `sstore` key costs `5` more gas and `90` more ticks: one key costs `5,274`, and the
cached total at 200M drops to `7,287,261,989`. -/
theorem decomposition_bridge_non_vacuous_and_tight :
    (5 : Nat) = 5 ∧ 2100 + 5 = 2105 ∧ 2060 + 90 + coldRow = 5274 ∧
      coldRow = 3124 ∧ perTx = 42382 ∧ mainCached200 = 7287261989 :=
  ⟨rfl, by decide, by decide, decomposition.2.2.2.2.1, decomposition.2.2.2.2.2, cached_slopes.1⟩

/-- 2. Cached joint LP at 200M: `451 × costC ≤ 3,058,910,053,880`. -/
theorem cached200_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * costC A K L B E n2 n17 md ms P T ≤ 3058910053880 :=
  cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 3. Cached joint LP at 380M: `11,803 × costC ≤ 118,511,584,702,912`. -/
theorem cached380_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912 :=
  cached380 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 4. Uncached full LP at 200M: `231 × costU ≤ 25,461,560,820,280`. -/
theorem uncached200_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 :=
  uncached200 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 5. Uncached full LP at 380M: `231 × costU ≤ 47,863,280,820,280`. -/
theorem uncached380_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280 :=
  uncached380 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 6. Cached totals: `7,287,261,989` (`123×` passes, `124×` fails) at 200M and
`10,545,558,216` (`85×` passes, `86×` fails) at 380M. -/
theorem cached_slopes_bridge_non_vacuous_and_tight :
    mainCached200 = 7287261989 ∧ 123 * mainCached200 < yukon ∧
      yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧
      yukon < 86 * mainCached380 :=
  cached_slopes

/-- 7. Uncached totals: `110,593,745,629` (`8×`) at 200M and `207,570,888,486` (`4×`) at 380M. -/
theorem uncached_slopes_bridge_non_vacuous_and_tight :
    mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧
      yukon < 5 * mainUncached380 :=
  uncached_slopes

/-- 8. The gain over the previous module is `1,581,510` ticks; sub-7·10⁹ is not reached. -/
theorem no_sub_seven_bridge_non_vacuous_and_tight :
    7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 287261989 ∧
      7288843499 - mainCached200 = 1581510 :=
  no_sub_seven

/-- 9. Nine-pass clock accounting: StackAlloc is identity outside stub 6, StackNames is an exact
isometry, and StackToLab has no bound linear in StackSem ticks. -/
theorem flapjack_nine_pass_clock_accounting_summary_bridge_non_vacuous_and_tight {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (dc : DataToWord.Config) (info : Spt Nat)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f)) :
    (∀ y ∈ InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.rawCallSections
        arch prog wc ac perf,
      y.1 ≠ storeConstsStubLocation → StackAlloc.progComp y = y) ∧
    (∀ (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
       (r : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (p, s) = (r, t) →
       ¬s.useAlloc → ¬s.useStore → ¬s.useStack →
       s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f) →
       StackSemEvaluate.evaluate (StackNames.progCompHOL f p, StackNames.renameState c f s) =
         (r, StackNames.renameState c f t) ∧
       (StackNames.renameState c f t).clock = t.clock) ∧
    (∀ (s : StackSemStateFiniteExact width C F) (t : LabSem.State width C F) (slope : Nat),
       s.clock = 0 →
       StackSemEvaluate.evaluate ((.skip : HolProg width), s) = (none, s) ∧
       (LabSem.evaluate {t with clock := slope * s.clock}).1 = .timeOut) :=
  InitECandidate.Solver.PanToStackNamesEndToEndLinearClockMaster.flapjack_nine_pass_clock_accounting_summary
    arch prog wc ac perf dc info c f hf

/-- 10. The 122-budget table: 122 strictly increasing budgets, last entry 900,719,810,000, margin
115,474 under Yukon. -/
theorem one_hundred_twenty_two_table_bridge_non_vacuous_and_tight :
    OneHundredTwentyTwoShape ∧
    oneHundredTwentyTwoExplicitBudgets.length = 122 ∧
    oneHundredTwentyTwoExplicitBudgets.getLast? = some 900719810000 ∧
    yukon - 900719810000 = 115474 :=
  ⟨one_hundred_twenty_two_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_two_budget_last_margin_non_vacuous_and_tight.2.2⟩

end InitECandidate.Solver.SstoreDirtyKeyGasOneHundredTwentyThreeXAndOneHundredTwentyTwoBudgetBridge
