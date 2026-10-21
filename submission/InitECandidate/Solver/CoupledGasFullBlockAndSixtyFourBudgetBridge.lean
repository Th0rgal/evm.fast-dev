import InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster
import InitECandidate.Solver.FullBlockTransientProbesAndSixtyTwoBudgetBridge
import InitECandidate.Solver.FullBlockTransientProbesAndSixtyFourBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.CoupledGasFullBlockAndSixtyFourBudgetBridge`

Bridge between the gas-coupled full block, the 62-budget probe bridge, and the
64-budget master.

* Under the shared `200,000,000` gas budget, a side regime at `≤ 50,000` ticks per unit
  is absorbed into the `10¹¹` quadratic term. So `ts+64` at `10 · L` ticks per unit adds
  nothing for every `L ≤ 5,000`: the block stays `224,985,309,693` (heap) and
  `195,654,540,749` (memoized), with `4 × 195,654,540,749 = 782,618,162,996` under Yukon.
* Coupling raises the caps: `L ≤ 38,786` and `L ≤ 40,253` at slope one, `L ≤ 5,009` and
  `L ≤ 6,476` at slope four. The next value crosses, and the unsalted run `158,162` still
  fails both.
* The 64 budgets grow strictly under Yukon `900,719,925,474`, and each finite certificate
  is conditional on the base certificate.
-/

namespace InitECandidate.Solver.CoupledGasFullBlockAndSixtyFourBudgetBridge

open InitECandidate.Solver.GuestCoupledGasFullBlockWithProbesAndTransientMaster
open InitECandidate.Solver.FullBlockTransientProbesAndSixtyFourBudgetMaster

/-- 1. Absorption: `L ≤ 5,000` reverting stores on the shared budget stay in `10¹¹`. -/
theorem absorbed_non_vacuous_and_tight (L n u B blk : Nat) (hL : L ≤ 5000) (hu : n ≤ u)
    (hS : B + u ≤ 2000000) (hblk : 40 * blk ≤ B * B) :
    blk + 10 * L * n ≤ 100000000000 :=
  absorbed L n u B blk hL hu hS hblk

/-- 2. No excess below the threshold; the first excess appears at `L = 5,001`. -/
theorem excess_non_vacuous_and_tight (L : Nat) (h : L ≤ 5000) :
    excess L = 0 ∧ excess 5001 = 20000000 :=
  ⟨excess_zero L h, excess_first⟩

/-- 3. For every `L ≤ 5,000` the full block equals the probe subtotals. -/
theorem block_unchanged_non_vacuous_and_tight (L : Nat) (h : L ≤ 5000) :
    coupled GuestFullBlockWithTransientStorageAndProbesMaster.subHeap L = 224985309693 ∧ coupled GuestFullBlockWithTransientStorageAndProbesMaster.subMemo L = 195654540749 :=
  block_unchanged L h

/-- 4. The fourfold memoized subtotal stays under Yukon. -/
theorem fourfold_non_vacuous_and_tight :
    4 * GuestFullBlockWithTransientStorageAndProbesMaster.subMemo = 782618162996 ∧ 4 * GuestFullBlockWithTransientStorageAndProbesMaster.subMemo < GuestJointBlockGasHtabBound.yukon :=
  ⟨slopes_non_vacuous_and_tight.1, slopes_non_vacuous_and_tight.2.1⟩

/-- 5. Coupled cap at slope one, heap: `L = 38,786` fits, `38,787` crosses. -/
theorem lmax_one_heap_non_vacuous_and_tight :
    coupled GuestFullBlockWithTransientStorageAndProbesMaster.subHeap 38786 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon ≤ coupled GuestFullBlockWithTransientStorageAndProbesMaster.subHeap 38787 :=
  lmax1_heap

/-- 6. Coupled cap at slope one, memoized: `L = 40,253` fits, `40,254` crosses. -/
theorem lmax_one_memo_non_vacuous_and_tight :
    coupled GuestFullBlockWithTransientStorageAndProbesMaster.subMemo 40253 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon ≤ coupled GuestFullBlockWithTransientStorageAndProbesMaster.subMemo 40254 :=
  lmax1_memo

/-- 7. Coupled cap at slope four, heap: `L = 5,009` fits, `5,010` crosses. -/
theorem lmax_four_heap_non_vacuous_and_tight :
    4 * coupled GuestFullBlockWithTransientStorageAndProbesMaster.subHeap 5009 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon ≤ 4 * coupled GuestFullBlockWithTransientStorageAndProbesMaster.subHeap 5010 :=
  lmax4_heap

/-- 8. Coupled cap at slope four, memoized: `L = 6,476` fits, `6,477` crosses. -/
theorem lmax_four_memo_non_vacuous_and_tight :
    4 * coupled GuestFullBlockWithTransientStorageAndProbesMaster.subMemo 6476 < GuestJointBlockGasHtabBound.yukon ∧
      GuestJointBlockGasHtabBound.yukon ≤ 4 * coupled GuestFullBlockWithTransientStorageAndProbesMaster.subMemo 6477 :=
  lmax4_memo

/-- 9. The unsalted run `158,162` still exceeds both coupled caps at slope one. -/
theorem unsalted_non_vacuous_and_tight :
    40253 < 158162 ∧ GuestJointBlockGasHtabBound.yukon < coupled GuestFullBlockWithTransientStorageAndProbesMaster.subMemo 158162 ∧
      GuestJointBlockGasHtabBound.yukon < coupled GuestFullBlockWithTransientStorageAndProbesMaster.subHeap 158162 :=
  unsalted_still_fails

/-- 10. The 64 budgets grow strictly under Yukon, and each finite certificate needs the
base certificate. -/
theorem portfolio_64_non_vacuous_and_tight
    (cert : UnrolledTwelveCandidatePortfolio.CertificateAt 1212035192) :
    SixtyFourShape ∧ ClaimPayloads ∧
      (∀ K ∈ portfolio,
        InitE.Certificate (SelfContainedBoundedCertificate.baselineWithFiniteK K) (.finite K)) :=
  certificates_non_vacuous_and_tight cert

end InitECandidate.Solver.CoupledGasFullBlockAndSixtyFourBudgetBridge
