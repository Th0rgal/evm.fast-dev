import InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
import InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge
import InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyBudgetBridge

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
open InitECandidate.Solver.TxGasCoupledOneHundredTwentyTwoXAndOneHundredTwentyBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. One `G`-independent block constant `370,538,614`; a cold row costs `3,124`; one transaction
costs `42,382`; one key costs `5,184` and one account `3,473`. -/
theorem decomposition_bridge_non_vacuous_and_tight :
    blockFixed = 370538614 ∧ coldRow = 3124 ∧ perTx = 42382 ∧
      2060 + coldRow = 5184 ∧ 349 + coldRow = 3473 ∧
      gasRows200 = 341086592 ∧ gasRows380 = 625505600 :=
  ⟨rfl, decomposition.2.2.2.2.1, decomposition.2.2.2.2.2, by decide, by decide,
   decomposition.1, decomposition.2.1⟩

/-- 2. Cached joint LP at 200M: `99 × costC ≤ 671,624,630,120`. -/
theorem cached200_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    99 * costC A K L B E n2 n17 md ms P T ≤ 671624630120 :=
  cached200 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 3. Cached joint LP at 380M: `11,803 × costC ≤ 118,511,584,702,912`. -/
theorem cached380_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912 :=
  cached380 A K L B E n2 n17 md ms P T hg h1 h2 hb he hw

/-- 4. Uncached full LP at 200M: `231 × costU ≤ 25,461,560,820,280`. -/
theorem uncached200_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 :=
  uncached200 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 5. Uncached full LP at 380M: `231 × costU ≤ 47,863,280,820,280`. -/
theorem uncached380_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280 :=
  uncached380 A K L B E n2 n17 md ms P C T hg h1 h2 hb he hw

/-- 6. Cached totals: `7,288,843,499` (`123×` passes, `124×` fails) at 200M and
`10,545,558,216` (`85×` passes, `86×` fails) at 380M. -/
theorem cached_slopes_bridge_non_vacuous_and_tight :
    mainCached200 = 7288843499 ∧ 123 * mainCached200 < yukon ∧
      yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧
      yukon < 86 * mainCached380 :=
  cached_slopes

/-- 7. Uncached totals: `110,593,745,629` (`8×`) at 200M and `207,570,888,486` (`4×`) at 380M. -/
theorem uncached_slopes_bridge_non_vacuous_and_tight :
    mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
      yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧
      yukon < 5 * mainUncached380 :=
  uncached_slopes

/-- 8. Sub-7·10⁹ is not reached: `mainCached200` is `288,843,499` above it. -/
theorem no_sub_seven_bridge_non_vacuous_and_tight :
    7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 288843499 ∧
      mainCached200 - 6993799055 = 295044444 :=
  no_sub_seven

/-- 9. `stateRelHOL` pins the three StackNames flags on the target and the source flags, and the
clocks stay aligned. -/
theorem stateRelHOL_target_flags_bridge_non_vacuous_and_tight {C F : Type} {jump : Bool}
    {bounds : BitVec width × BitVec width} {pointer : Nat}
    {source target : StackSemStateFiniteExact width C F}
    (h : stateRelHOL jump bounds pointer source target) :
    ¬target.useAlloc ∧ ¬target.useStore ∧ ¬target.useStack ∧
      source.useStack = true ∧ source.useStore = true ∧ source.useAlloc = false ∧
      target.clock = source.clock :=
  let f := InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge.stateRelHOL_target_flags h
  ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2.1, f.2.2.2.2.2,
   (InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge.stateRelHOL_compile_and_clock h).2⟩

/-- 10. The 120-budget table: 120 strictly increasing budgets, last entry 900,719,800,000, margin
125,474 under Yukon. -/
theorem one_hundred_twenty_table_bridge_non_vacuous_and_tight :
    OneHundredTwentyShape ∧
    oneHundredTwentyExplicitBudgets.length = 120 ∧
    oneHundredTwentyExplicitBudgets.getLast? = some 900719800000 ∧
    yukon - 900719800000 = 125474 :=
  ⟨one_hundred_twenty_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_budget_last_margin_non_vacuous_and_tight.2.2⟩

end InitECandidate.Solver.ColdWalkBalMergeOneHundredTwentyThreeXAndOneHundredTwentyBudgetBridge
