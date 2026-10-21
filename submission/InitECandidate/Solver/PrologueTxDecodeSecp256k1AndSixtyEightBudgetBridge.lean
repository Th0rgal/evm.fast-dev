import InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
import InitECandidate.Solver.EndToEndStartToHaltCoupledMptAndSixtySixBudgetBridge
import InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSixtyEightBudgetBridge`

Bridge between the prologue and post-EVM bound, the 66-budget coupled-MPT bridge, and
the 68-budget master.

* At `12,000` intrinsic gas a block holds `16,666` user transactions plus 2 system
  transactions. Sender recovery costs `30,000 · 16,668 = 500,040,000`, the two indexed
  tries cost `2 · 130,000 · 16,666 = 4,333,160,000`, and `logs_bloom` costs `26,666,650`:
  together `post_evm = 4,859,866,650`.
* Added to the coupled totals: `229,226,116,343` (heap) exceeds the fourfold quarter
  `225,179,981,368`, so `4×` fails without memoization; `199,895,347,399` (memoized)
  leaves `25,284,633,969` at `4×` (`188` ticks per input byte) and `671,493,809,131` at
  `1×` (`5,003` ticks per input byte).
* The 68 budgets grow strictly under Yukon `900,719,925,474`, and each finite certificate
  is conditional on the base certificate.
-/

namespace InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSixtyEightBudgetBridge

open InitECandidate.Solver.GuestPrologueTxDecodeSecp256k1AndIndexedMptBound
open InitECandidate.Solver.EndToEndCoupledMptStackRemoveZeroAndSixtyEightBudgetMaster

/-- 1. Transaction cap: `200,000,000 / 12,000 = 16,666` user transactions. -/
theorem tx_count_non_vacuous_and_tight (t : Nat) (h : 12000 * t ≤ 200000000) :
    t ≤ 16666 ∧ 200000000 / 12000 = 16666 :=
  ⟨(tx_count t h).1, by decide⟩

/-- 2. Sender recovery, indexed tries and logs bloom. -/
theorem post_parts_non_vacuous_and_tight :
    30000 * 16668 = 500040000 ∧ 2 * 130000 * 16666 = 4333160000 ∧
      500040000 + 4333160000 + 26666650 = 4859866650 := by
  decide

/-- 3. Their sum is the post-EVM term. -/
theorem post_evm_non_vacuous_and_tight : postTerms = 4859866650 := post_val

/-- 4. Block total with the post-EVM term, heap: `229,226,116,343`. -/
theorem block_with_post_heap_non_vacuous_and_tight :
    block_total_coupled_mpt + postTerms = 229226116343 := by
  decide

/-- 5. Fourfold without memoization fails: the quarter `225,179,981,368` is below the total. -/
theorem fourfold_heap_fails_non_vacuous_and_tight :
    900719925474 / 4 = 225179981368 ∧ 225179981368 < 229226116343 := by
  decide

/-- 6. Block total with the post-EVM term, memoized: `199,895,347,399`. -/
theorem block_with_post_memo_non_vacuous_and_tight :
    block_total_memo_coupled_mpt + postTerms = 199895347399 := by
  decide

/-- 7. Fourfold memoized margin: `25,284,633,969`, i.e. `188` ticks per input byte. -/
theorem fourfold_memo_margin_non_vacuous_and_tight :
    900719925474 / 4 - 199895347399 = 25284633969 ∧
      188 * 134217712 ≤ 25284633969 ∧ 25284633969 < 189 * 134217712 := by
  decide

/-- 8. Slope-one margin: `671,493,809,131`, i.e. `5,003` ticks per input byte. -/
theorem one_margin_non_vacuous_and_tight :
    900719925474 - 229226116343 = 671493809131 ∧
      5003 * 134217712 ≤ 671493809131 ∧ 671493809131 < 5004 * 134217712 := by
  decide

/-- 9. The indexed tries dominate: they are at least `80 %` of the post-EVM term. -/
theorem tries_dominate_non_vacuous_and_tight : 10 * 4333160000 ≥ 8 * postTerms :=
  tries_dominate

/-- 10. The 68 budgets grow strictly under Yukon, and each finite certificate needs the
base certificate. -/
theorem portfolio_68_non_vacuous_and_tight
    (cert : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    SixtyEightShape ∧ ClaimPayloads ∧
      (∀ K ∈ portfolio,
        InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K)
          (.finite K)) :=
  sixty_eight_budget_certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.PrologueTxDecodeSecp256k1AndSixtyEightBudgetBridge
