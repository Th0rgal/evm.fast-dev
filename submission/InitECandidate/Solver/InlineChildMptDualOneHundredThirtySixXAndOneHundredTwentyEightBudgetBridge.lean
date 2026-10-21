import InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster
import InitECandidate.Solver.CrepToStackNamesAndLabToTargetEndToEndClockMaster
import InitECandidate.Solver.LoopToStackNamesLabToTargetAndOneHundredTwentyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.InlineChildMptDualOneHundredThirtySixXAndOneHundredTwentyEightBudgetBridge

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open InitECandidate.Solver.GuestInlineChildMptDualAndOneHundredThirtySixXMaster
open InitECandidate.Solver.LoopToStackNamesLabToTargetAndOneHundredTwentyEightBudgetMaster
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. Regime 1 at 200M (no `hb`): `451 × cost1 ≤ 3,058,910,053,880`. -/
theorem inline_200_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * cost1 A K L B E n2 n17 md ms P T ≤ 3058910053880 :=
  inline_200 A K L B E n2 n17 md ms P T hg h1 h2 he hw

/-- 2. Regime 1 at 380M: `451 × cost1 ≤ 4,809,020,803,880`. -/
theorem inline_380_bridge_non_vacuous_and_tight (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * cost1 A K L B E n2 n17 md ms P T ≤ 4809020803880 :=
  inline_380 A K L B E n2 n17 md ms P T hg h1 h2 he hw

/-- 3. Regime 2 at 200M (hashed children only): `11 × cost2 ≤ 66,779,086,680`. -/
theorem yp_200_bridge_non_vacuous_and_tight (A K L B E n2 d r md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    11 * cost2 A K L B E n2 d r md ms P T ≤ 66779086680 :=
  yp_200 A K L B E n2 d r md ms P T hg h1 h2 hb he hw

/-- 4. Regime 2 at 380M: `11 × cost2 ≤ 102,419,086,680`. -/
theorem yp_380_bridge_non_vacuous_and_tight (A K L B E n2 d r md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    11 * cost2 A K L B E n2 d r md ms P T ≤ 102419086680 :=
  yp_380 A K L B E n2 d r md ms P T hg h1 h2 hb he hw

/-- 5. Regime 2 is attained: all `PUSH31`, `6,100,805` dead-end branches. -/
theorem yp_tight_bridge_non_vacuous_and_tight :
    11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 ≤ 66779086680 ∧
      66779086680 - 11 * cost2 0 0 0 0 0 0 6100805 0 0 0 200000000 0 < 11 * 405 ∧
      7 * 0 + 22 * 6100805 ≤ inputBytes :=
  yp_tight

/-- 6. Regime 1: `7,287,261,989` (`123×` passes, `124×` fails) at 200M and
`11,167,773,630` (`80×` passes, `81×` fails) at 380M. -/
theorem inline_slopes_bridge_non_vacuous_and_tight :
    inline200 = 7287261989 ∧ 123 * inline200 < yukon ∧
      yukon < 124 * inline200 ∧ inline380 = 11167773630 ∧ 80 * inline380 < yukon ∧
      yukon < 81 * inline380 :=
  inline_slopes

/-- 7. Regime 2: `6,575,582,388` (`136×` passes, `137×` fails) at 200M and
`9,815,582,388` (`91×` passes, `92×` fails) at 380M. -/
theorem yp_slopes_bridge_non_vacuous_and_tight :
    yp200 = 6575582388 ∧ 136 * yp200 < yukon ∧ yukon < 137 * yp200 ∧
      yp380 = 9815582388 ∧ 91 * yp380 < yukon ∧ yukon < 92 * yp380 :=
  yp_slopes

/-- 8. Dropping `hb` costs `622,215,414` ticks at 380M (`85× → 80×`); nothing at 200M. -/
theorem hb_gap_bridge_non_vacuous_and_tight :
    inline380 - 10545558216 = 622215414 ∧ inline200 = 7287261989 :=
  hb_gap

/-- 9. A non-error Crep result stays non-error through `resultToLoop`, and regime 2 beats
regime 1 by `711,679,601` ticks at 200M. -/
theorem resultToLoop_ne_error_bridge_non_vacuous_and_tight
    (res : Option (CrepResultHOLExact width)) (h : res ≠ some .error) :
    resultToLoop res ≠ some .error ∧ inline200 - yp200 = 711679601 :=
  ⟨InitECandidate.Solver.CrepToStackNamesAndLabToTargetEndToEndClockMaster.resultToLoop_ne_error
      res h,
   by decide⟩

/-- 10. The 128-budget table: 128 strictly increasing budgets, last entry 900,719,840,000, margin
85,474 under Yukon. -/
theorem one_hundred_twenty_eight_table_bridge_non_vacuous_and_tight :
    OneHundredTwentyEightShape ∧
    oneHundredTwentyEightExplicitBudgets.length = 128 ∧
    oneHundredTwentyEightExplicitBudgets.getLast? = some 900719840000 ∧
    yukon - 900719840000 = 85474 :=
  ⟨one_hundred_twenty_eight_budget_portfolio_all_below_yukon_ceiling_non_vacuous_and_tight,
   one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.1,
   one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.2.1,
   one_hundred_twenty_eight_budget_last_margin_non_vacuous_and_tight.2.2⟩

end InitECandidate.Solver.InlineChildMptDualOneHundredThirtySixXAndOneHundredTwentyEightBudgetBridge
