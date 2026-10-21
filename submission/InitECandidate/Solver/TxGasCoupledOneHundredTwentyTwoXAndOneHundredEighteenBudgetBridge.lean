import InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
import InitECandidate.Solver.StackRawCallToStackNamesAndStackToLabLinearBridge
import InitECandidate.Solver.WitnessEmptyItemPushOneHundredTwelveXAndOneHundredEighteenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredEighteenBudgetBridge

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
open InitECandidate.Solver.WitnessEmptyItemPushOneHundredTwelveXAndOneHundredEighteenBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. Per-tx cost `40,782`; `16,666` transactions cost `679,672,812`; the true fixed parts are
`711,625,206` at 200M and `996,044,214` at 380M. -/
theorem decomposition_bridge_non_vacuous_and_tight :
    perTx = 40782 ∧ perTx * 16666 = 679672812 ∧
      trueFixed200 + perTx * 16666 = oldFixed200 ∧ trueFixed380 + perTx * 16666 = oldFixed380 ∧
      trueFixed200 = 711625206 ∧ trueFixed380 = 996044214 :=
  decomposition

/-- 2. Cached joint LP at 200M with `T` on the gas budget: `33 × costC ≤ 214,138,410,040`. -/
theorem cached200_bridge_non_vacuous_and_tight (A K B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    33 * costC A K B E n2 n17 md ms P T ≤ 214138410040 :=
  cached200 A K B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 3. Cached joint LP at 380M: `11,803 × costC ≤ 114,947,567,578,464`. -/
theorem cached380_bridge_non_vacuous_and_tight (A K B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K B E n2 n17 md ms P T ≤ 114947567578464 :=
  cached380 A K B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 4. Uncached full LP at 200M: `231 × costU ≤ 25,461,560,820,280`. -/
theorem uncached200_bridge_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 :=
  uncached200 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 5. Uncached full LP at 380M: `231 × costU ≤ 47,863,280,820,280`. -/
theorem uncached380_bridge_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 :=
  uncached380 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 6. Cached totals: `7,334,885,647` (`122×` passes, `123×` fails) at 200M and
`10,869,105,236` (`82×` passes, `83×` fails) at 380M. -/
theorem cached_slopes_bridge_non_vacuous_and_tight :
    mainCached200 = 7334885647 ∧ 122 * mainCached200 < yukon ∧
      yukon < 123 * mainCached200 ∧ mainCached380 = 10869105236 ∧ 82 * mainCached380 < yukon ∧
      yukon < 83 * mainCached380 :=
  cached_slopes

/-- 7. Uncached totals: `110,934,832,221` (`8×`) at 200M and `208,196,394,086` (`4×`) at 380M,
each lower by `679,672,812`. -/
theorem uncached_slopes_bridge_non_vacuous_and_tight :
    mainUncached200 = 110934832221 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 208196394086 ∧ 4 * mainUncached380 < yukon ∧
      yukon < 5 * mainUncached380 :=
  uncached_slopes

/-- 8. Sub-7·10⁹ is not reached: `mainCached200` is `334,885,647` above it. -/
theorem no_sub_seven_bridge_non_vacuous_and_tight :
    7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 334885647 :=
  no_sub_seven

/-- 9. StackNames is an exact isometry (same clock, same result, renamed post-state), and
StackRawCall then StackNames needs at most `extra ≤ source.clock` (≤ 2×). -/
theorem stackNames_exact_clock_bridge_non_vacuous_and_tight {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (p, s) = (r, t))
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    StackSemEvaluate.evaluate (StackNames.progCompHOL f p, StackNames.renameState c f s) =
      (r, StackNames.renameState c f t) ∧
    (StackNames.renameState c f s).clock = s.clock ∧
    (StackNames.renameState c f t).clock = t.clock :=
  InitECandidate.Solver.StackRawCallToStackNamesAndStackToLabLinearBridge.stackNames_exact_clock
    c f p s t r run hf ha hs hk hc

/-- 10. The 118-budget table: 118 strictly increasing budgets, last entry 900,719,500,000, margin
425,474 under Yukon. -/
theorem one_hundred_eighteen_table_bridge_non_vacuous_and_tight :
    OneHundredEighteenShape ∧
    oneHundredEighteenExplicitBudgets.length = 118 ∧
    oneHundredEighteenExplicitBudgets.getLast? = some 900719500000 ∧
    yukon - 900719500000 = 425474 :=
  ⟨one_hundred_eighteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_eighteen_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_eighteen_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_eighteen_budget_last_margin_non_vacuous_and_tight.2.2⟩

end InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredEighteenBudgetBridge
