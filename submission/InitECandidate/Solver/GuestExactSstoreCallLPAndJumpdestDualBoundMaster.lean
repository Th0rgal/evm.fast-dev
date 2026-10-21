import InitECandidate.Solver.GuestExactSstoreCallTicksAndTxCoupledSubSevenBillionMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster`

Two complete bounds, one gas budget.

**Bound 1 — current Guest (uncached `compute_jumpdests`).** A `CALL`-family frame costs
`≥ 126` gas and `≤ 67,884` ticks: scan `65,536` + bitmap `memzero` `1,026` + `op_call`-family
straight line `≤ 294`… we use `349 + 28` rounded into a `1,000`-tick slack (`frame_new` 28,
child prologue). Per unit of 100 gas: calls `≈ 53,876` ticks, far above `PUSH31` (`1,800`),
keys (`(1,950 + 110)/21`), accounts (`349/24`) and the per-tx top-level scan
(`66,562` per `12,000` gas): the max puts all gas in calls. Gas in hundredths:
`2400 A + 2100 K + 100 P + 126 C + 12000 T ≤ G`.

**Bound 2 — jumpdest cache per code.** Each distinct code scanned once (`≤ I` ticks). Exact
charges `110`/key and `349`/account in the global LP. The rational simplex optimum puts all gas
in `PUSH31` and an all-empty witness: `1,800 · units + 90 · I/4`. So the cached bound is
`8,145,414,250` (`110×`) at 200M and `11,669,833,258` (`77×`) at 380M, not `129×`/`85×`:
the exact charges only shrink rows that are not on the optimum.
-/

namespace InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def inputBytes : Nat := 134217712
def fixed200 : Nat := 1391298018
def fixed380 : Nat := 1675717026
def callTicks : Nat := 65536 + 1026 + 294 + 28 + 1000

/-- Uncached: EVM + calls + per-tx scans + witness. -/
def costU (A K P C T m : Nat) : Nat :=
  349 * A + 2060 * K + 18 * P + callTicks * C + 66562 * T + 90 * m

/-- Cached: the global LP of `GuestGlobalGasCoupledEvmAndSubNineBillionMaster` with exact charges. -/
def costC (A K B E n2 n17 m P : Nat) : Nat :=
  349 * A + 2060 * K + 633 * B + 439 * E + 138 * n2 + 416 * n17 + 90 * m + 1800 * P

def mainUncached200 : Nat := fixed200 + (callTicks * 200000000 / 126 + 90 * (inputBytes / 4))
def mainUncached380 : Nat := fixed380 + (callTicks * 380000000 / 126 + 90 * (inputBytes / 4))
def mainCached200 : Nat := fixed200 + inputBytes + 6619898520
def mainCached380 : Nat := fixed380 + inputBytes + 9859898520

/-- 1. Per-call ticks `67,884`. -/
theorem call_val : callTicks = 67884 := by decide

/-- 2. **Uncached joint bound at 200M** (any mix; `P` in gas units). -/
theorem uncached200 (A K P C T m : Nat)
    (hg : 2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 200000000) (hw : 4 * m ≤ inputBytes) :
    costU A K P C T m ≤ callTicks * 200000000 / 126 + 90 * (inputBytes / 4) := by
  unfold costU callTicks inputBytes at *; omega

/-- 3. **Uncached joint bound at 380M.** -/
theorem uncached380 (A K P C T m : Nat)
    (hg : 2400 * A + 2100 * K + 1 * P + 126 * C + 12000 * T ≤ 380000000) (hw : 4 * m ≤ inputBytes) :
    costU A K P C T m ≤ callTicks * 380000000 / 126 + 90 * (inputBytes / 4) := by
  unfold costU callTicks inputBytes at *; omega

/-- 4. **Current Guest: `8×` at 200M, `4×` at 380M (guaranteed).** -/
theorem uncached_slopes : mainUncached200 = 112163577490 ∧ 8 * mainUncached200 < yukon ∧
    yukon < 9 * mainUncached200 ∧ mainUncached380 = 209425139355 ∧ 4 * mainUncached380 < yukon ∧
    yukon < 5 * mainUncached380 := by decide

/-- 5. **Cached joint LP at 200M** with exact charges. -/
theorem cached200 (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 2000000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    costC A K B E n2 n17 m P ≤ 6619898520 := by
  unfold costC inputBytes at *; omega

/-- 6. **Cached joint LP at 380M.** -/
theorem cached380 (A K B E n2 n17 m P : Nat) (hg : 24 * A + 21 * K + P ≤ 3800000)
    (h1 : B + E ≤ 82 * A + 63 * K) (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ n17 + K + A) (he : E ≤ n2 + 2 * (K + A)) (hw : 7 * n2 + 22 * n17 + 4 * m ≤ inputBytes) :
    costC A K B E n2 n17 m P ≤ 9859898520 := by
  unfold costC inputBytes at *; omega

/-- 7. Optimum attained: all `PUSH31`, empty witness entries. -/
theorem cached_tight : costC 0 0 0 0 0 0 (inputBytes / 4) 2000000 = 6619898520 ∧
    costC 0 0 0 0 0 0 (inputBytes / 4) 3800000 = 9859898520 := by decide

/-- 8. **Cached Guest: `110×` at 200M, `77×` at 380M.** -/
theorem cached_slopes : mainCached200 = 8145414250 ∧ 110 * mainCached200 < yukon ∧
    yukon < 111 * mainCached200 ∧ mainCached380 = 11669833258 ∧ 77 * mainCached380 < yukon ∧
    yukon < 78 * mainCached380 := by decide

end InitECandidate.Solver.GuestExactSstoreCallLPAndJumpdestDualBoundMaster
