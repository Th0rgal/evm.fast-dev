import InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit
import InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis`

1. `_resolve_step` probes. `_resolve_step` is called `≤ 16` times per branch, `≤ 1` per extension.
   Its fixed cost (`≤ 6` ticks: `rlp_item`, `nodedb_lookup`, `htab_get`, `htab_find_slot`,
   `htab_hash`, `node_new_hashed`) is already inside `GuestWitnessDecodeExactTicksPerByteAudit`.
   The extra cost is `2` ticks per `htab_find_slot` probe step (`while` body + `memeq` call).
   With an average probe run `r`, the extra is `2 · r · calls`.
2. Block total = gas envelope `156,088,992,805` + MPT/`nodedb` builds `20,036,870,848` + decode.

**Caveat (not hidden):** `156,088,992,805` is `kPanElevenTablesShared`, the envelope **without**
the transient table `ts+64`. With `ts+64` and `REVERT` the gas term exceeds Yukon on its own
(`GuestTransientStorageAndRemainingTablesAudit`), so `block_total` below is a total **conditional
on `ts+64` being fixed** (salted `htab_hash`), not a bound on the current Guest.
-/

namespace InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge (mptPlusBuild)

def gasEnv : Nat := 156088992805
def decodeHeap : Nat := 31092374808
def decodeMemo : Nat := 10938743528

/-- Total `_resolve_step` calls from `B` branches and `E` extensions. -/
def resolveCalls (E B : Nat) : Nat := 16 * B + E

/-- 1. Heap case: branch count `≤ 69,402,622` gives `≤ 1,110,441,952` branch resolves. -/
theorem resolve_heap (B : Nat) (h : B ≤ 69402622) : resolveCalls 0 B ≤ 1110441952 := by
  unfold resolveCalls; omega

/-- 2. Memoized case: `≤ 33,554,428` nodes give `≤ 536,870,848` calls (any mix `E + B ≤ n`). -/
theorem resolve_memo (E B : Nat) (h : E + B ≤ 33554428) : resolveCalls E B ≤ 536870848 := by
  unfold resolveCalls; omega

/-- 3. Exact probe ticks: `2 · r · calls`. At `r = 8`: `17,767,071,232` (heap) and
`8,589,933,568` (memo). -/
theorem probe_at_8 : 2 * 8 * 1110441952 = 17767071232 ∧ 2 * 8 * 536870848 = 8589933568 := by decide

/-- 4. **Block total without memoization**: `207,218,238,461`, margin `693,501,687,013`. -/
theorem block_total : gasEnv + mptPlusBuild + decodeHeap = 207218238461 ∧
    yukon - (gasEnv + mptPlusBuild + decodeHeap) = 693501687013 := by decide

/-- 5. **Block total with memoization**: `187,064,607,181`, margin `713,655,318,293`. -/
theorem block_total_memo : gasEnv + mptPlusBuild + decodeMemo = 187064607181 ∧
    yukon - (gasEnv + mptPlusBuild + decodeMemo) = 713655318293 := by decide

/-- 6. Slope `4×` fits both totals; `5×` fails both. -/
theorem slope_four : 4 * 207218238461 < yukon ∧ yukon < 5 * 207218238461 ∧
    4 * 187064607181 = 748258428724 ∧ 4 * 187064607181 < yukon ∧ yukon < 5 * 187064607181 := by
  decide

/-- 7. Probe-run threshold in the Yukon margin, heap case: `r ≤ 312`, `313` fails. -/
theorem r_threshold_heap : 2 * 312 * 1110441952 ≤ 693501687013 ∧
    693501687013 < 2 * 313 * 1110441952 := by decide

/-- 8. Probe-run threshold, memo case: `r ≤ 664`, `665` fails. -/
theorem r_threshold_memo : 2 * 664 * 536870848 ≤ 713655318293 ∧
    713655318293 < 2 * 665 * 536870848 := by decide

/-- 9. With probes, block total stays under Yukon for any `r ≤ 312` (heap case). -/
theorem total_with_probes (B r : Nat) (hB : B ≤ 69402622) (hr : r ≤ 312) :
    gasEnv + mptPlusBuild + decodeHeap + 2 * r * resolveCalls 0 B < yukon := by
  have h1 := resolve_heap B hB
  have h2 : 2 * r * resolveCalls 0 B ≤ 2 * 312 * 1110441952 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr) h1
  have h3 : gasEnv + mptPlusBuild + decodeHeap + 2 * 312 * 1110441952 < yukon := by
    unfold gasEnv decodeHeap mptPlusBuild; decide
  omega

/-- 10. Without a salt the run is attacker-controlled: one key-crafted run of length `cap / 2 =
2^25` per call already exceeds the margin. -/
theorem unsalted_breaks : 693501687013 < 2 * 2 ^ 25 * 1110441952 := by decide

/-- 11. Memoization value of the decode term. -/
theorem memo_saving : decodeHeap - decodeMemo = 20153631280 := by decide

end InitECandidate.Solver.GuestWitnessResolveAndBlockTotalTicksSynthesis
