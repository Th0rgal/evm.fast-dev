import InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSixtyEightBudgetBridge
import InitECandidate.Solver.StackRemoveZeroClockPrologueSecp256k1AndSixtyEightBudgetBridge
import InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.PrologueSecp256k1AndSeventyBudgetBridge`

Bridge between the 68-budget prologue bridge, the stack-remove zero-clock bridge, and
the 70-budget master.

* Post-EVM: `secp256k1_recover = 500,040,000`, the two indexed tries `4,333,160,000`,
  `logs_bloom = 26,666,650`, summing to `post_evm = 4,859,866,650`.
* What remains for the prologue: `671,493,809,131` at slope one (`5,003` ticks per input
  byte) and `25,284,633,969` at fourfold with memoization (`188` ticks per byte).
* With the post-EVM term inside the total, the caps are `L ≤ 38,574` and `L ≤ 40,041`
  at slope one, and `L ≤ 6,264` at fourfold memoized. The next value crosses Yukon.
* The 70 budgets grow strictly under Yukon `900,719,925,474`, and each finite certificate
  is conditional on the base certificate.
-/

namespace InitECandidate.Solver.PrologueSecp256k1AndSeventyBudgetBridge

open InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSeventyBudgetMaster

/-- Total once the `ts+64` excess over the absorbed range is added. -/
def withExcess (base L : Nat) : Nat := base + (10 * L - 50000) * 2000000

/-- 1. The three post-EVM terms and their sum. -/
theorem post_evm_bridge_non_vacuous_and_tight :
    30000 * 16668 = 500040000 ∧ 2 * 130000 * 16666 = 4333160000 ∧
      50 * 533333 = 26666650 ∧ post_evm = 4859866650 := by
  decide

/-- 2. Block totals with the post-EVM term: `229,226,116,343` and `199,895,347,399`. -/
theorem block_totals_bridge_non_vacuous_and_tight :
    block_total = 229226116343 ∧ block_total_memo = 199895347399 :=
  ⟨block_totals_non_vacuous_and_tight.1, block_totals_non_vacuous_and_tight.2.1⟩

/-- 3. Slope-one margin: `671,493,809,131`, i.e. `5,003` ticks per input byte. -/
theorem one_margin_non_vacuous_and_tight :
    900719925474 - block_total = 671493809131 ∧
      5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712 := by
  decide

/-- 4. Fourfold memoized margin: `25,284,633,969`, i.e. `188` ticks per input byte. -/
theorem fourfold_memo_margin_bridge_non_vacuous_and_tight :
    900719925474 / 4 - block_total_memo = 25284633969 ∧
      188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712 := by
  decide

/-- 5. Fourfold without memoization fails: the quarter is below the heap total. -/
theorem fourfold_heap_fails_non_vacuous_and_tight :
    900719925474 / 4 = 225179981368 ∧ 225179981368 < block_total :=
  ⟨fourfold_heap_refuted_non_vacuous_and_tight.1, fourfold_heap_refuted_non_vacuous_and_tight.2.1⟩

/-- 6. Cap at slope one, heap: `L = 38,574` fits, `38,575` crosses. -/
theorem lmax_one_heap_non_vacuous_and_tight :
    withExcess block_total 38574 < 900719925474 ∧
      900719925474 ≤ withExcess block_total 38575 := by
  decide

/-- 7. Cap at slope one, memoized: `L = 40,041` fits, `40,042` crosses. -/
theorem lmax_one_memo_non_vacuous_and_tight :
    withExcess block_total_memo 40041 < 900719925474 ∧
      900719925474 ≤ withExcess block_total_memo 40042 := by
  decide

/-- 8. Cap at fourfold, memoized: `L = 6,264` fits, `6,265` crosses. -/
theorem lmax_four_memo_non_vacuous_and_tight :
    4 * withExcess block_total_memo 6264 < 900719925474 ∧
      900719925474 ≤ 4 * withExcess block_total_memo 6265 := by
  decide

/-- 9. Transaction ceiling: `16,666` user transactions plus 2 system transactions. -/
theorem tx_ceiling_non_vacuous_and_tight :
    12000 * 16666 ≤ 200000000 ∧ 200000000 < 12000 * 16667 ∧ 16666 + 2 = 16668 :=
  transaction_ceiling_non_vacuous_and_tight.2

/-- 10. The 70 budgets grow strictly under Yukon, and each finite certificate needs the
base certificate. -/
theorem portfolio_70_non_vacuous_and_tight
    (cert : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    SeventyShape ∧
      (∀ K ∈ portfolio,
        InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K)
          (.finite K)) :=
  seventy_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.PrologueSecp256k1AndSeventyBudgetBridge
