import InitECandidate.Solver.GuestColdWalkBalMergeGasCoupledSubSevenBillionMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster`

`op_sstore` (l.7499), read line by line: a cold key is charged `access_cost = 2100` plus
`10000` only when `original == current ≠ new` (`oc ∧ ¬cn`). A no-op or "same as original"
store pays exactly `2,100` (no `+100` warm read: that is EIP-2929 for `SLOAD`, not this code).
`set_storage` (l.5767) always `jset`s the key, so `compute_state_root` (l.14660) runs
`mpt_set` on every touched key, and `_mpt_insert_node` calls `node_invalidate` on each node of
the path even when the value is unchanged: a no-op key still dirties its `≤ 63` nodes and pays
the full rehash. Hence `K` cannot be split into a cheap clean class; `2,100` gas per dirty key
is exact and `5,000` is not a lower bound.

Only real tightening: a cold `SSTORE` needs its key and value on the stack, `≥ PUSH0 (2) +
PUSHn (3)` gas, so `≥ 2,105` gas per key, and `≤ 90` extra ticks (`13 + 59 + slack`).
-/

namespace InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster

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
  (349 + coldRow) * A + (2060 + 90 + coldRow) * K + coldRow * L + 633 * B + 439 * E + 127 * n2 +
    405 * n17 + 43 * md + 79 * ms + 18 * P + perTx * T
def costU (A K L B E n2 n17 md ms P C T : Nat) : Nat :=
  costC A K L B E n2 n17 md ms P T + 67884 * C + 66562 * T

def mainCached200 : Nat := blockFixed + inputBytes + (3058910053880 + 450) / 451
def mainCached380 : Nat := blockFixed + inputBytes + (118511584702912 + 11802) / 11803
def mainUncached200 : Nat := blockFixed + (25461560820280 + 230) / 231
def mainUncached380 : Nat := blockFixed + (47863280820280 + 230) / 231

/-- 1. Exact decomposition: one `G`-independent block constant. -/
theorem decomposition : gasRows200 = 341086592 ∧ gasRows380 = 625505600 ∧
    trueFixed200 = blockFixed + gasRows200 ∧ trueFixed380 = blockFixed + gasRows380 ∧
    coldRow = 3124 ∧ perTx = 42382 := by decide

/-- 2. **Cached, 200M.** -/
theorem cached200 (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    451 * costC A K L B E n2 n17 md ms P T ≤ 3058910053880 := by
  unfold costC coldRow perTx inputBytes at *; omega

/-- 3. **Cached, 380M.** -/
theorem cached380 (A K L B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K L B E n2 n17 md ms P T ≤ 118511584702912 := by
  unfold costC coldRow perTx inputBytes at *; omega

/-- 4. **Uncached, 200M.** -/
theorem uncached200 (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 25461560820280 := by
  unfold costU costC coldRow perTx inputBytes at *; omega

/-- 5. **Uncached, 380M.** -/
theorem uncached380 (A K L B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K L B E n2 n17 md ms P C T ≤ 47863280820280 := by
  unfold costU costC coldRow perTx inputBytes at *; omega

/-- 6. **Cached: `123×` at 200M, `85×` at 380M.** -/
theorem cached_slopes : mainCached200 = 7287261989 ∧ 123 * mainCached200 < yukon ∧
    yukon < 124 * mainCached200 ∧ mainCached380 = 10545558216 ∧ 85 * mainCached380 < yukon ∧
    yukon < 86 * mainCached380 := by decide

/-- 7. **Uncached: `8×` / `4×`.** -/
theorem uncached_slopes : mainUncached200 = 110593745629 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 207570888486 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 := by decide

/-- 8. Gain over the previous module is only `1,581,510` ticks; sub-7·10⁹ not reached. -/
theorem no_sub_seven : 7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 287261989 ∧
    7288843499 - mainCached200 = 1581510 := by decide

end InitECandidate.Solver.GuestSstoreDirtyKeyGasAndSubSevenBillionMaster
