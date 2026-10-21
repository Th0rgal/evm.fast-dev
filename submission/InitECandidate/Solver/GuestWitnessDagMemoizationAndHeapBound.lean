import InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound`

Hand transcription of `guest.pp.pnk` (wt-2). Heap bytes allocated per decoded node (from the code,
not the request's `64 / 112 / 176`):
* leaf: `rlp_list_to_slices` `2·16 = 32` + `compact_to_nibbles` `alloc(2n) ≥ 2` + `node_new_leaf` `64`
  ⇒ `≥ 98`;
* extension: `32 + 2 + node_new_ext 56` ⇒ `≥ 90` (the explicit-stack record is `scratch_alloc(88)`,
  scratch, not heap);
* branch: `17·16 = 272` + `node_new_branch 176` ⇒ `≥ 448`.
Minimum is the extension: `90` bytes. Heap available `31,092,374,808`.

Ticks per node are **not** counted exactly here. Every loop in the node path (`rlp_list_to_slices`,
`key_to_nibbles`, `memzero`, 17 `_resolve_step`s) is linear in the node's heap bytes, so the model
is `ticks ≤ τ · heapBytes` (+ `nodedb_lookup` probes, absent forced collisions). Results are stated
for a rate `τ` and give the exact Yukon threshold.
-/

namespace InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def heapAvail : Nat := 33806089496 - 2713714688

/-- Heap bytes of a decoded set of `L` leaves, `E` extensions, `B` branches (lower bounds). -/
def heapOf (L E B : Nat) : Nat := 98 * L + 90 * E + 448 * B

/-- 1. Heap available. -/
theorem heap_avail_val : heapAvail = 31092374808 := by decide

/-- 2. Node count under the heap: `L + E + B ≤ 345,470,831`. -/
theorem nodes_by_heap (L E B : Nat) (h : heapOf L E B ≤ heapAvail) : L + E + B ≤ 345470831 := by
  unfold heapOf heapAvail at h; omega

/-- 3. Tight: `345,470,831` extensions fit. -/
theorem nodes_by_heap_tight : heapOf 0 345470831 0 ≤ heapAvail ∧ heapAvail < heapOf 0 345470832 0 := by
  decide

/-- 4. Branch count under the heap: `B ≤ 69,402,622`. -/
theorem branches_by_heap (B : Nat) (h : heapOf 0 0 B ≤ heapAvail) : B ≤ 69402622 := by
  unfold heapOf heapAvail at h; omega

/-- 5. **Heap bound** (unmodified Guest): `ticks ≤ τ · heapBytes ≤ τ · 31,092,374,808`. -/
theorem decode_heap_bound (τ bytes : Nat) (h : bytes ≤ heapAvail) : τ * bytes ≤ τ * 31092374808 := by
  unfold heapAvail at h; exact Nat.mul_le_mul_left _ h

/-- 6. Yukon threshold for the heap bound: `τ ≤ 28` ticks per heap byte. -/
theorem heap_threshold : 28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808 := by decide

/-- 7. With `5×` slope: `τ ≤ 5`. -/
theorem heap_threshold_5x : 5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808) := by
  decide

/-- 8. **DAG memoization**: each `nodedb` entry decoded once ⇒ `L + E + B ≤ 33,554,428`. -/
theorem nodes_memo (L E B n : Nat) (hn : 4 * n ≤ 134217712) (h : L + E + B ≤ n) :
    L + E + B ≤ 33554428 := by omega

/-- 9. Memoized heap model: fixed `≤ 448` bytes per node plus `≤ 2` heap bytes per input byte
(nibble buffers / slice arrays proportional to the node payload), assumed, not recounted. -/
theorem memo_heap : 448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 15300819168 < heapAvail := by
  decide

/-- 10. Memoized decode ticks `≤ τ · 15,301,819,168`: Yukon threshold `τ ≤ 58`. -/
theorem memo_threshold : 58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168 := by decide

/-- 11. Memoization halves the worst heap (and the tick bound) at least: `2 · 15.3 G ≤ 31.1 G`. -/
theorem memo_gain : 2 * 15300819168 ≤ heapAvail := by decide

end InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound
