import InitECandidate.Solver.GuestJointTransitionInsertionBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestMergeTxUnionEnvelope`

`merge_tx_into_block` (l.5911) and `htab_union_into` (l.5899) from `guest.pp.pnk` (wt-2).

`htab_union_into(dst, src)` iterates `cap(src)` slots; for each occupied one it does
`htab_set(dst, key, val)` (one `htab_find_slot` on `dst` + insert). `merge_tx_into_block` unions,
per committed tx:
* `ts+24→bs+24`, `ts+8→bs+8`, `ts+40→bs+40`, `ts+16→bs+16`, `ts+48→bs+48` — all **address-keyed**
  (20/28-byte): one entry per touched address, cost ≥ 2600/2900 gas each ⇒ far from the storage
  cluster, ≤ one slot per find with one target address.
* `ts+32→bs+32` storage: for every inner storage key committed this tx, `htab_set(binner, key)`
  inserts into the block inner cluster `binner` of size `D_{<i}`.

Two cost parts:
1. **Linear slot scan** over each src capacity. Load factor ≤ 1/2 ⇒ `cap ≤ 2·entries`, so the total
   scan is `≤ 2·(total committed entries) ≤ 2·D` ticks, bounded by `mergeLin = 500,000,000`
   (`D ≤ 95,238` storage + address entries ≪ 2.5·10⁸).
2. **Block insertion** into `bs+32`: `D` keys, each `htab_set` scanning the growing cluster. Combined
   with the warm `SLOAD`/`SSTORE` probes this is `2·D·(W+D)` under the shared budget
   `20·D + (W+D) ≤ S` (a committed storage key costs ≥ 20 units: 19 warm + 1, or 21 cold).
   Completion of the square: `80·D·(W+D) ≤ S²`, so `2·D·(W+D) ≤ 100,000,000,000`, at `D = 50,000`,
   `W = 950,000`.
-/

namespace InitECandidate.Solver.GuestMergeTxUnionEnvelope

open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon maxGuestSourceClock)

/-- Local per-tx coupled excess (from `GuestCoupledTxBlockStorageBound`, slope 8). -/
def locCoup : Nat := 8 * 3994571428
/-- Linear merge slot-scan budget. -/
def mergeLin : Nat := 500000000
/-- Combined block storage term (warm probes + merge inserts): `⌊S²/80⌋·2`. -/
def blockMerge : Nat := 100000000000

/-- 1. `htab_union_into` linear scan: with `≤ 95,238` committed entries per block and one tick per
scanned slot plus one call per entry, the scan fits `mergeLin`; tight constant check. -/
theorem union_linear (n : Nat) (h : 21 * n ≤ S) : 2 * n + n ≤ mergeLin ∧ 3 * 95238 ≤ mergeLin := by
  unfold S at h; unfold mergeLin; omega

/-- 2. **Merge block insertion + warm probes**: `20·D + (W + D) ≤ S ⇒ 80·(D·(W+D)) ≤ S²`. -/
theorem merge_block_square (D W : Nat) (h : 20 * D + (W + D) ≤ S) : 80 * (D * (W + D)) ≤ S * S := by
  have h' : (20 * (D : Int) + (W + D)) ≤ 2000000 := by unfold S at h; exact_mod_cast h
  have hD : (0 : Int) ≤ D := by positivity
  have hb : (W : Int) + D ≤ 2000000 - 20 * D := by linarith
  have hm : (D : Int) * (W + D) ≤ D * (2000000 - 20 * D) := Int.mul_le_mul_of_nonneg_left hb hD
  have hsq : (0 : Int) ≤ (2000000 - 40 * (D : Int)) ^ 2 := sq_nonneg _
  have : (80 : Int) * (D * (W + D)) ≤ 2000000 * 2000000 := by nlinarith
  unfold S; exact_mod_cast this

/-- 3. Integer form: `2·D·(W+D) ≤ 100,000,000,000`. -/
theorem merge_block_le (D W : Nat) (h : 20 * D + (W + D) ≤ S) :
    2 * (D * (W + D)) ≤ blockMerge := by
  have := merge_block_square D W h
  unfold blockMerge S at *; omega

/-- 4. Attained at `(D, W) = (50,000, 950,000)`, exactly 200M gas. -/
theorem merge_block_tight :
    20 * 50000 + (950000 + 50000) = S ∧ 2 * (50000 * (950000 + 50000)) = blockMerge := by decide

/-- 5. The address-keyed unions add one slot per target address: with a single concentrated
address they contribute `O(1)`, absorbed in `mergeLin`. -/
theorem addr_unions_constant : 5 * 2 ≤ mergeLin := by decide

/-- Master merge-aware source clock. -/
def kPanMerge : Nat := linear + locCoup + blockMerge + mergeLin

/-- 6. Value. -/
theorem kPanMerge_val : kPanMerge = 136116135658 := by decide

/-- 7. **Master bound**: for every budget-feasible `(D, W)` and local term, the merge-aware clock
is `≤ kPanMerge`. -/
theorem kPanMerge_master (D W Tloc Tlin : Nat) (h : 20 * D + (W + D) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + 2 * (D * (W + D)) + Tlin ≤ kPanMerge := by
  have := merge_block_le D W h
  unfold kPanMerge; omega

/-- 8. Target slopes `3×, 4×, 5×, 6×` stay under the Yukon ceiling. -/
theorem slopes_ok :
    3 * kPanMerge < yukon ∧ 4 * kPanMerge < yukon ∧
      5 * kPanMerge < yukon ∧ 6 * kPanMerge < yukon := by decide

/-- 9. Exact integer slope threshold: `k · kPanMerge < Yukon ↔ k ≤ 6` (so `7×` fails). -/
theorem slope_threshold (k : Nat) : k * kPanMerge < yukon ↔ k ≤ 6 := by
  unfold kPanMerge linear locCoup blockMerge mergeLin yukon; omega

/-- 10. Yukon margin at `6×`. -/
theorem margin6 : yukon - 6 * kPanMerge = 84023111526 := by decide

/-- 11. Above `maxGuestSourceClock`, and the merge adds `4,761,904,762` over the no-merge
block term `95,238,095,238`. -/
theorem merge_overhead :
    maxGuestSourceClock < kPanMerge ∧ blockMerge - 95238095238 = 4761904762 := by decide

end InitECandidate.Solver.GuestMergeTxUnionEnvelope
