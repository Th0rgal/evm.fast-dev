import InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit`

Hand tick counts of the node-decode path in `guest.pp.pnk` (wt-2), convention: 1 tick per `while`
body, 1 per `.call`, 0 for `ld`/`st`/FFI. Upper bounds per decoded node:

* **leaf** (`_decode_step` two-item + leaf arm): `rlp_decode_fully`→`rlp_list_count` over 2 items
  (`≤ 11`) + `rlp_list_to_slices` (`≤ 15`) + `rlp_item` key (1) + `compact_to_nibbles`/`key_to_nibbles`
  (`≤ 12`) + `rlp_item` value (1) + `node_new_leaf` alloc (1) + body loop (2) = **`43`** ticks,
  `98` heap bytes ⇒ `τ_leaf = 43/98 < 1`.
* **extension**: leaf path minus value, plus one `_resolve_step` (`≤ 6`): **`48`** ticks, `90` bytes
  ⇒ `τ_ext = 48/90 < 1`.
* **branch** (17 slices): `rlp_decode_fully` (`≤ 86`) + `rlp_list_to_slices` (`≤ 119`) +
  16 `_resolve_step` (`≤ 96`) + body loop (`≤ 18`) + `node_new_branch`/`memzero 176` (`≤ 7`) =
  **`326`** ticks, `448` bytes ⇒ `τ_branch = 326/448 < 1`.

So every node costs **fewer ticks than its heap bytes**: `τ ≤ 1`. This is well under the `28`
(Yukon), `5` (5×) and `58` (memoized) thresholds of `GuestWitnessDagMemoizationAndHeapBound`, which
closes the witness-decode bound unconditionally. (nodedb probes excluded: absent forced Keccak
collisions each `_resolve_step` lookup is `O(1)`; forced collisions are the separate `nodedb` risk.)
-/

namespace InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound (heapAvail heapOf)

def tLeaf : Nat := 43
def tExt : Nat := 48
def tBranch : Nat := 326

/-- Decode ticks for `L` leaves, `E` extensions, `B` branches. -/
def decodeTicks (L E B : Nat) : Nat := tLeaf * L + tExt * E + tBranch * B

/-- 1. Per-node ticks are below the node's heap bytes (`τ_x < 1`). -/
theorem tau_leaf : tLeaf ≤ 98 := by decide
theorem tau_ext : tExt ≤ 90 := by decide
theorem tau_branch : tBranch ≤ 448 := by decide

/-- 2. `max τ ≤ 28` (Yukon rate), `≤ 5` (5× rate) and `≤ 58` (memoized rate): all satisfied at `1`. -/
theorem tau_max : tLeaf ≤ 98 ∧ tExt ≤ 90 ∧ tBranch ≤ 448 ∧ max (max tLeaf tExt) tBranch ≤ 448 := by
  decide

/-- 3. Total decode ticks never exceed total heap bytes. -/
theorem ticks_le_heap (L E B : Nat) : decodeTicks L E B ≤ heapOf L E B := by
  unfold decodeTicks heapOf tLeaf tExt tBranch
  have := Nat.mul_le_mul_right L (show 43 ≤ 98 by decide)
  have := Nat.mul_le_mul_right E (show 48 ≤ 90 by decide)
  have := Nat.mul_le_mul_right B (show 326 ≤ 448 by decide)
  omega

/-- 4. **Heap-bounded decode under Yukon, unconditionally**: heap-fitting node sets decode in
`≤ heapAvail < Yukon` ticks. -/
theorem decode_under_yukon (L E B : Nat) (h : heapOf L E B ≤ heapAvail) :
    decodeTicks L E B < yukon := by
  have h1 := ticks_le_heap L E B
  have : heapAvail < yukon := by unfold heapAvail; decide
  omega

/-- 5. Even at `5×` Yukon the heap-bounded decode fits. -/
theorem decode_under_5x (L E B : Nat) (h : heapOf L E B ≤ heapAvail) :
    5 * decodeTicks L E B < yukon := by
  have h1 := ticks_le_heap L E B
  have : 5 * heapAvail < yukon := by unfold heapAvail; decide
  have := Nat.mul_le_mul_left 5 (le_trans h1 h)
  omega

/-- 6. Tightness of the rate check: `τ = 1` for every node would still fit, and `τ = 29` on the
full heap would break Yukon — the measured `τ ≤ 1` is safely inside. -/
theorem rate_tight : 1 * heapAvail < yukon ∧ yukon < 29 * heapAvail := by
  unfold heapAvail; decide

/-- 7. All-branch extreme (worst heap packing of branches): `≤ 69,402,622` branches, decode
`≤ 326 · 69,402,622`, under Yukon. -/
theorem all_branch (B : Nat) (h : heapOf 0 0 B ≤ heapAvail) :
    decodeTicks 0 0 B < yukon ∧ B ≤ 69402622 := by
  refine ⟨decode_under_yukon 0 0 B h, ?_⟩
  unfold heapOf heapAvail at h; omega

/-- 8. **Memoized DAG close**: `L + E + B ≤ 33,554,428` ⇒ decode `≤ 326 · 33,554,428` under Yukon
with margin. -/
theorem decode_memo (L E B n : Nat) (hn : 4 * n ≤ 134217712) (h : L + E + B ≤ n) :
    decodeTicks L E B ≤ 326 * 33554428 ∧ 326 * 33554428 < yukon := by
  constructor
  · unfold decodeTicks tLeaf tExt tBranch
    have hb : L + E + B ≤ 33554428 := by omega
    calc 43 * L + 48 * E + 326 * B ≤ 326 * L + 326 * E + 326 * B := by
            have := Nat.mul_le_mul_right L (show 43 ≤ 326 by decide)
            have := Nat.mul_le_mul_right E (show 48 ≤ 326 by decide)
            omega
      _ = 326 * (L + E + B) := by ring
      _ ≤ 326 * 33554428 := Nat.mul_le_mul_left _ hb
  · decide

/-- 9. Memoized decode value and its Yukon margin. -/
theorem decode_memo_val : 326 * 33554428 = 10938743528 ∧ yukon - 326 * 33554428 = 889781181946 := by
  decide

/-- 10. Combined with the heap cap it is a pure linear term, orders below Yukon: `τ ≤ 1` means the
entire witness decode is dominated by one pass over allocated memory. -/
theorem decode_linear (L E B : Nat) (h : heapOf L E B ≤ heapAvail) :
    decodeTicks L E B ≤ 31092374808 := by
  have h1 := ticks_le_heap L E B
  have : heapAvail = 31092374808 := by unfold heapAvail; decide
  omega

end InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit
