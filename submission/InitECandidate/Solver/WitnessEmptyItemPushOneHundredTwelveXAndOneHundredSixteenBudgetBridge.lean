import InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
import InitECandidate.Solver.StackRawCallLinearClockAndOneHundredSixteenBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.WitnessEmptyItemPushOneHundredTwelveXAndOneHundredSixteenBudgetBridge

open InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster
open InitECandidate.Solver.StackRawCallLinearClockAndOneHundredSixteenBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. Empty-item keccak costs 35 ticks; one `PUSH31` costs 54 = 18 × 3. -/
theorem leaf_counts_bridge_non_vacuous_and_tight :
    keccakEmpty = 35 ∧ push31 = 54 ∧ push31 = 18 * 3 :=
  leaf_counts

/-- 2. Cached joint LP at 200M: `33 × costC ≤ 214,138,410,040`. -/
theorem cached200_bridge_non_vacuous_and_tight (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    33 * costC A K B E n2 n17 md ms P ≤ 214138410040 :=
  cached200 A K B E n2 n17 md ms P hg h1 h2 hb he hw

/-- 3. Cached joint LP at 380M: `11,803 × costC ≤ 114,947,567,578,464`. -/
theorem cached380_bridge_non_vacuous_and_tight (A K B E n2 n17 md ms P : Nat)
    (hg : 2400 * A + 2100 * K + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K B E n2 n17 md ms P ≤ 114947567578464 :=
  cached380 A K B E n2 n17 md ms P hg h1 h2 hb he hw

/-- 4. Uncached full LP at 200M: `231 × costU ≤ 25,461,560,820,280`. -/
theorem uncached200_bridge_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 :=
  uncached200 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 5. Uncached full LP at 380M: `231 × costU ≤ 47,863,280,820,280`. -/
theorem uncached380_bridge_non_vacuous_and_tight (A K B E n2 n17 md ms P C T : Nat)
    (hg : 2400 * A + 2100 * K + P + 126 * C + 12000 * T ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 :=
  uncached380 A K B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 6. Cached totals: `8,014,558,459` (`112×` passes, `113×` fails) at 200M and
`11,548,778,048` (`77×` passes, `78×` fails) at 380M. -/
theorem cached_slopes_bridge_non_vacuous_and_tight :
    mainCached200 = 8014558459 ∧ 112 * mainCached200 < yukon ∧
      yukon < 113 * mainCached200 ∧ mainCached380 = 11548778048 ∧ 77 * mainCached380 < yukon ∧
      yukon < 78 * mainCached380 :=
  cached_slopes

/-- 7. Uncached totals: `111,614,505,033` (`8×` passes, `9×` fails) at 200M and
`208,876,066,898` (`4×` passes, `5×` fails) at 380M. -/
theorem uncached_slopes_bridge_non_vacuous_and_tight :
    mainUncached200 = 111614505033 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 208876066898 ∧ 4 * mainUncached380 < yukon ∧
      yukon < 5 * mainUncached380 :=
  uncached_slopes

/-- 8. `135×` is not reached: it needs `main ≤ 6,671,999,447`. -/
theorem no_135_bridge_non_vacuous_and_tight :
    yukon / 135 = 6671999447 ∧ yukon < 135 * mainCached200 :=
  no_135

/-- 9. The 116-budget table: 116 strictly increasing budgets, last entry 900,718,000,000, margin
1,925,474 under Yukon. -/
theorem one_hundred_sixteen_table_bridge_non_vacuous_and_tight :
    OneHundredSixteenShape ∧
    oneHundredSixteenExplicitBudgets.length = 116 ∧
    oneHundredSixteenExplicitBudgets.getLast? = some 900718000000 ∧
    yukon - 900718000000 = 1925474 :=
  ⟨one_hundred_sixteen_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_sixteen_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_sixteen_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_sixteen_budget_last_margin_non_vacuous_and_tight.2.2⟩

/-- 10. Every one of the 116 budgets carries a finite certificate, from one base certificate. -/
theorem one_hundred_sixteen_certificates_bridge_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) :
    OneHundredSixteenShape ∧
    (∀ K ∈ oneHundredSixteenExplicitBudgets,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  one_hundred_sixteen_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.WitnessEmptyItemPushOneHundredTwelveXAndOneHundredSixteenBudgetBridge
