import InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster`

Gas-dependent rows still inside `trueFixed` (GSN `walks`, GXM `balTicks`, merge, opcode table,
bloom): `341,086,592` at 200M, `625,505,600` at 380M. Removing them leaves the same
`blockFixed = 370,538,614` at both gas limits.

**Who pays the `3,124` ticks.** Walk (`1,300`), BAL (`1,440`) and merge (`384`) are charged per
cold access. The cold accesses of the LP are exactly the accounts `A` and keys `K` (the `2,060`
key rate is `1,950` walk/find + `110` SSTORE and contains no BAL/merge row; the `349` account
rate contains neither). So `3,124` is added to `A` and `K`, plus an extra variable `L` for
cold accesses that are neither (`≥ 1,900` gas). Putting it only on a fresh `L` would erase these
rows for the `A`/`K` that the optimum actually uses. Each user tx pays `40,782 + 1,600` bloom.
-/

namespace InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
  (trueFixed200 trueFixed380)

def inputBytes : Nat := 134217712
def coldRow : Nat := 1300 + 1440 + 384
def perTx : Nat := 40782 + 1600
def gasRows200 : Nat := 130000000 + 144000000 + 40420992 + 1600 * 16666
def gasRows380 : Nat := 247000000 + 273600000 + 76800000 + 1440000 + 1600 * 16666
def blockFixed : Nat := 370538614

def costC (A K L B E n2 n17 md ms P T : Nat) : Nat :=
  (349 + coldRow) * A + (2060 + coldRow) * K + coldRow * L + 633 * B + 439 * E + 127 * n2 +
    405 * n17 + 43 * md + 79 * ms + 18 * P + perTx * T
def costU (A K L B E n2 n17 md ms P C T : Nat) : Nat :=
  costC A K L B E n2 n17 md ms P T + 67884 * C + 66562 * T

def mainCached200 : Nat := blockFixed + inputBytes + (671624630120 + 98) / 99
def mainCached380 : Nat := blockFixed + inputBytes + (118511584702912 + 11802) / 11803
def mainUncached200 : Nat := blockFixed + (25461560820280 + 230) / 231
def mainUncached380 : Nat := blockFixed + (47863280820280 + 230) / 231

/-- 1. Exact decomposition: one `G`-independent block constant. -/
theorem decomposition : gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
    trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
    coldRow = 3124 ∧ perTx = 42382 := by decide

/-- 2. **Cached, 200M.** -/
theorem cached200 (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    99 * costC A K L B E n2 n17 md ms P T ≤ 671624630120 := by
  unfold costC coldRow perTx inputBytes at *; omega

/-- 3. **Cached, 380M.** -/
theorem cached380 (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912 := by
  unfold costC coldRow perTx inputBytes at *; omega

/-- 4. **Uncached, 200M.** -/
theorem uncached200 (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 := by
  unfold costU costC coldRow perTx inputBytes at *; omega

/-- 5. **Uncached, 380M.** -/
theorem uncached380 (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + 1900 * L + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280 := by
  unfold costU costC coldRow perTx inputBytes at *; omega

/-- 6. **Cached: `123×` at 200M, `85×` at 380M.** -/
theorem cached_slopes : mainCached200 = 7288843499 ∧ 123 * mainCached200 < yukon ∧
    yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧
    yukon < 86 * mainCached380 := by decide

/-- 7. **Uncached: `8×` / `4×`.** -/
theorem uncached_slopes : mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 := by decide

/-- 8. Sub-7·10⁹ is not reached once the cold rows stay on `A`/`K`. -/
theorem no_sub_seven : 7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 288843499 ∧
    mainCached200 - 6993799055 = 295044444 := by decide

end InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster
