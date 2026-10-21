import InitECandidate.Solver.GuestWitnessEmptyItemAndPushExactTicksMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster`

**Per-tx rows inside the old `fixed` (from `GuestSaltedNodedbWitnessMptAndSubTwentyBillionAudit`,
`GuestExactMergeBalPrologueAndSeventyFiveXMaster`), at `T = 16,666` user txs:**
* `secp256k1_recover` (l.2375 via `recover_sender` l.5268): `30,000` per tx
  (`500,040,000 = 30,000 · 16,668`; the 2 system lines stay fixed);
* tx + receipt trie rehash: `2 · 7 · 663 = 9,282` per tx (`154,693,812`);
* merge per-tx overhead `1,500` (`merge_tx_into_block` l.5911; the 2 system lines stay fixed).
So `perTx = 40,782`, `40,782 · 16,666 = 679,672,812`. BAL is per key, not per tx, and is
already gas-bounded: it is not moved. The `50,213`/`8,640`/`3,600` figures are not in the chain.

Each user tx pays `12,000` gas (`calculate_intrinsic_cost` l.5298) out of the same `G`.
`40,782 / 12,000 < 4` ticks/gas, below `PUSH31` (`18`) and the key/account rows: the joint
optimum takes `T = 0`, so the `679,672,812` ticks leave both bounds.
-/

namespace InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def perTx : Nat := 30000 + 2 * 7 * 663 + 1500
def oldFixed200 : Nat := 1391298018
def oldFixed380 : Nat := 1675717026
def trueFixed200 : Nat := oldFixed200 - perTx * 16666
def trueFixed380 : Nat := oldFixed380 - perTx * 16666

def costC (A K B E n2 n17 md ms P T : Nat) : Nat :=
  349 * A + 2060 * K + 633 * B + 439 * E + 127 * n2 + 405 * n17 + 43 * md + 79 * ms + 18 * P +
    perTx * T
def costU (A K B E n2 n17 md ms P C T : Nat) : Nat :=
  costC A K B E n2 n17 md ms P T + 67884 * C + 66562 * T

def mainCached200 : Nat := trueFixed200 + inputBytes + (214138410040 + 32) / 33
def mainCached380 : Nat := trueFixed380 + inputBytes + (114947567578464 + 11802) / 11803
def mainUncached200 : Nat := trueFixed200 + (25461560820280 + 230) / 231
def mainUncached380 : Nat := trueFixed380 + (47863280820280 + 230) / 231

/-- 1. Exact decomposition of the old fixed rows. -/
theorem decomposition : perTx = 40782 ∧ perTx * 16666 = 679672812 ∧
    trueFixed200 + perTx * 16666 = oldFixed200 ∧ trueFixed380 + perTx * 16666 = oldFixed380 ∧
    trueFixed200 = 711625206 ∧ trueFixed380 = 996044214 := by decide

/-- 2. **Cached, 200M, `T` on the gas budget.** -/
theorem cached200 (A K B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    33 * costC A K B E n2 n17 md ms P T ≤ 214138410040 := by
  unfold costC perTx inputBytes at *; omega

/-- 3. **Cached, 380M.** -/
theorem cached380 (A K B E n2 n17 md ms P T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    11803 * costC A K B E n2 n17 md ms P T ≤ 114947567578464 := by
  unfold costC perTx inputBytes at *; omega

/-- 4. **Uncached, 200M** (per-tx scan and per-tx rows both on the gas budget). -/
theorem uncached200 (A K B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P + 126 * C ≤ 200000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 25461560820280 := by
  unfold costU costC perTx inputBytes at *; omega

/-- 5. **Uncached, 380M.** -/
theorem uncached380 (A K B E n2 n17 md ms P C T : Nat)
    (hg : 12000 * T + 2400 * A + 2100 * K + P + 126 * C ≤ 380000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * n17 + 4 * md + 5 * ms ≤ inputBytes) :
    231 * costU A K B E n2 n17 md ms P C T ≤ 47863280820280 := by
  unfold costU costC perTx inputBytes at *; omega

/-- 6. **Cached: `7,334,885,647` (`122×`) at 200M; `10,869,105,236` (`82×`) at 380M.** -/
theorem cached_slopes : mainCached200 = 7334885647 ∧ 122 * mainCached200 < yukon ∧
    yukon < 123 * mainCached200 ∧ mainCached380 = 10869105236 ∧ 82 * mainCached380 < yukon ∧
    yukon < 83 * mainCached380 := by decide

/-- 7. **Uncached: `8×` / `4×`, each lower by `679,672,812`.** -/
theorem uncached_slopes : mainUncached200 = 110934832221 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 208196394086 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 := by decide

/-- 8. Sub-7·10⁹ is not reached: it needs `335 M` more. -/
theorem no_sub_seven : 7000000000 < mainCached200 ∧ mainCached200 - 7000000000 = 334885647 := by
  decide

end InitECandidate.Solver.GuestTxGasCoupledFixedDecompositionAndSubSevenBillionMaster
