import InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
import InitECandidate.Solver.PanToWordToStackNamesSimulationAndClockMaster
import InitECandidate.Solver.SstoreDirtyKeyGasOneHundredTwentyThreeXAndOneHundredTwentyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.PanToWordToStackNamesAndOneHundredTwentyFourBudgetBridge

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
open InitECandidate.Solver.SstoreDirtyKeyGasOneHundredTwentyThreeXAndOneHundredTwentyFourBudgetMaster
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

/-- 9. LoopToWord runs the Word target at exactly the Loop source clock (no `ck`), and one key
costs `5,274` ticks. -/
theorem loopToWord_exact_clock_bridge_non_vacuous_and_tight {C F : Type}
    (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat)
    (run : LoopSemStateFiniteExact.evaluate prog s = (res, s1)) (ne : res ≠ some .error)
    (rel : loopToWordStateRelHOLExact s t)
    (loc : LoopToWord.localsRelHOL ctxt s.locals t.locals)
    (h0 : sptLookup 0 t.locals = some retv) (gd : goodDimindex width)
    (nw : ¬ wordSemIsWordLoc retv = true)
    (acc : ∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt) :
    (∃ t1 res1, WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt prog l).1
        { t with clock := s.clock } = (res1, t1) ∧ t1.ffi = s1.ffi) ∧
    2060 + 90 + coldRow = 5274 :=
  ⟨InitECandidate.Solver.PanToWordToStackNamesSimulationAndClockMaster.loopToWord_exact_clock
      prog s res s1 t ctxt retv l run ne rel loc h0 gd nw acc,
   by decide⟩

/-- 10. The 124-budget table: 124 strictly increasing budgets, last entry 900,719,820,000, margin
105,474 under Yukon. -/
theorem one_hundred_twenty_four_table_bridge_non_vacuous_and_tight :
    OneHundredTwentyFourShape ∧
    oneHundredTwentyFourExplicitBudgets.length = 124 ∧
    oneHundredTwentyFourExplicitBudgets.getLast? = some 900719820000 ∧
    yukon - 900719820000 = 105474 :=
  ⟨one_hundred_twenty_four_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_twenty_four_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_four_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_four_budget_last_margin_non_vacuous_and_tight.2.2⟩

end InitECandidate.Solver.PanToWordToStackNamesAndOneHundredTwentyFourBudgetBridge
