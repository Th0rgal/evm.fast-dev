import InitECandidate.Solver.GuestDirtyWriteHtabDominance

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestBs32BlockStorageEnvelope`

Joint block envelope on `(ts+*, bs+72, bs+32)` for `Guest/guest.pp.pnk` under one 200M-gas block
(`2,000,000` units of 100 gas, ≤ 11 EIP-7825 transactions).

Tick sources (hand transcription, disjoint):
* `T1` — `bs+32` block storage: `D` cold no-op `SSTORE`s (21 units, `set_storage`→`jset`→
  `merge_tx_into_block`) then `W` warm `SLOAD`s (1 unit) missing in `stor_lookup(bs+32)`:
  `T1 = 2·D·W`.
* `T3` — `bs+72` pre-state reads (`record_pre_state_read`, l.5517): `C` cold accesses (≥ 21 units):
  `T3 = blkRead C = 3·C·(C−1)/2`.
* `T2` — per-tx `ts+*`/`ev+*` scans. Since `ts+32` is now known to be filled at 21 units too, all
  7 `op_sstore` finds are cheap: slope `14`, per-tx term `11 · 4,925,802,697 = 54,183,829,667`
  (`GuestBlockVsTxHtabBounds.per_tx_sstore_ticks`). `T2` may reuse the same gas units as `T1`
  (a warm `SLOAD` scans `ts+24`/`ev+176` *and* `bs+32`), so it is bounded independently.
* Linear: prologue + `18·gas`.

Joint step: `T1` and `T3` are charged on disjoint operations (`D` storage keys, `C` addresses),
so `21·D + W + 21·C ≤ 2·10⁶` (stated as a hypothesis — it fails only if one 21-unit op creates both
a new `bs+72` address and a new `bs+32` key). Then `42·(T1 + T3) ≤ (2·10⁶)²`: the maximum sits at the
vertex `C = 0` (the objective is convex along the budget line), giving `95,238,095,238`.

Results: `kPanBs32Joint = 153,081,489,139` (partition) and `166,686,761,248` (unconditional sum).
Target slopes `3×` pass under Yukon; `6×`, `9×`, `12×` **fail**; the largest passing integer slope
is `5×`.
-/

namespace InitECandidate.Solver.GuestBs32BlockStorageEnvelope

open InitECandidate.Solver.GuestBlockVsTxHtabBounds (blkRead blkRead_closed blkRead_le)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon maxGuestSourceClock)

/-- Block units of 100 gas. -/
def S : Nat := 2000000
/-- Linear part: prologue + `18 · 200M`. -/
def linear : Nat := 59564234 + 18 * 200000000
/-- Per-tx term at slope 14 over 11 transactions. -/
def perTx : Nat := 11 * 4925802697
/-- Joint `bs+32` + `bs+72` maximum `⌊S²/42⌋`. -/
def blockJoint : Nat := 95238095238

/-- Joint envelope with partition hypothesis. -/
def kPanBs32Joint : Nat := linear + perTx + blockJoint
/-- Unconditional sum of individual maxima. -/
def kPanBs32Sum : Nat := linear + perTx + 13605272109 + 95238095238

/-- 1. Extracted constants. -/
theorem constants : linear = 3659564234 ∧ perTx = 54183829667 ∧ blockJoint = S * S / 42 := by
  decide

/-- 2. `bs+32` alone: `21·D + W ≤ S ⇒ 84·D·W ≤ S²`, i.e. `2·D·W ≤ 95,238,095,238`. -/
theorem bs32_alone (D W : Nat) (h : 21 * D + W ≤ S) : 2 * (D * W) ≤ blockJoint := by
  have := InitECandidate.Solver.GuestDirtyWriteHtabDominance.bs32_term_le D W h
  unfold InitECandidate.Solver.GuestDirtyWriteHtabDominance.pBs32 at this
  unfold blockJoint; omega

/-- 3. **Joint `bs+32` + `bs+72`** under one budget: `42·(2DW + blkRead C) ≤ S²`. -/
theorem bs32_bs72_joint (D W C : Nat) (h : 21 * D + W + 21 * C ≤ S) :
    42 * (2 * (D * W) + blkRead C) ≤ S * S := by
  have hb := blkRead_closed C
  have hcc : C * (C - 1) ≤ C * C := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h' : (21 * (D : Int) + W + 21 * C) ≤ 2000000 := by unfold S at h; exact_mod_cast h
  have e1 : (84 : Int) * (D * W) ≤ (21 * D + W) ^ 2 := by nlinarith [sq_nonneg ((21 : Int) * D - W)]
  have hA : (0 : Int) ≤ 21 * D + W := by positivity
  have hA2 : (21 * (D : Int) + W) ≤ 2000000 - 21 * C := by linarith
  have e2 : (21 * (D : Int) + W) ^ 2 ≤ (2000000 - 21 * C) ^ 2 := pow_le_pow_left₀ hA hA2 2
  have hC : (0 : Int) ≤ C := by positivity
  have e3 : (0 : Int) ≤ C * (2000000 - 21 * C) := mul_nonneg hC (by linarith)
  have key : (84 : Int) * (D * W) + 63 * (C * C) ≤ 2000000 * 2000000 := by nlinarith
  have key' : 84 * (D * W) + 63 * (C * C) ≤ 2000000 * 2000000 := by exact_mod_cast key
  unfold S; omega

/-- 4. The joint bound is attained at the vertex `(D, W, C) = (47,619, 1,000,001, 0)`. -/
theorem joint_vertex_tight :
    21 * 47619 + 1000001 + 21 * 0 = S ∧ 2 * (47619 * 1000001) + blkRead 0 = blockJoint := by
  decide

/-- 5. The other vertex (`W = D = 0`, all cold reads) gives only `13,605,272,109`. -/
theorem joint_other_vertex : blkRead 95238 = 13605272109 ∧ 13605272109 < blockJoint :=
  ⟨(blkRead_le 95238 (by decide)).2, by decide⟩

/-- 6. Joint `bs+*` term in ticks: `2DW + blkRead C ≤ 95,238,095,238`. -/
theorem block_terms_le (D W C : Nat) (h : 21 * D + W + 21 * C ≤ S) :
    2 * (D * W) + blkRead C ≤ blockJoint := by
  have := bs32_bs72_joint D W C h
  unfold blockJoint; unfold S at this; omega

/-- 7. Master envelope values. -/
theorem kPan_values : kPanBs32Joint = 153081489139 ∧ kPanBs32Sum = 166686761248 := by decide

/-- 8. Master bound: every partition-feasible `(D, W, C)` with any per-tx `T2 ≤ perTx` stays under
`kPanBs32Joint`. -/
theorem kPan_master (D W C T2 : Nat) (h : 21 * D + W + 21 * C ≤ S) (h2 : T2 ≤ perTx) :
    linear + T2 + (2 * (D * W) + blkRead C) ≤ kPanBs32Joint := by
  have := block_terms_le D W C h
  unfold kPanBs32Joint; omega

/-- 9. Envelope sits above `maxGuestSourceClock` (43.9 G) and under the Yukon ceiling. -/
theorem kPan_between : maxGuestSourceClock < kPanBs32Joint ∧ kPanBs32Sum < yukon := by decide

/-- 10. Slope `3×`: passes under Yukon for both envelopes. -/
theorem slope3_ok : 3 * kPanBs32Joint < yukon ∧ 3 * kPanBs32Sum < yukon := by decide

/-- 11. Slopes `6×`, `9×`, `12×` exceed Yukon even with the joint partition envelope. -/
theorem slope_6_9_12_fail :
    yukon < 6 * kPanBs32Joint ∧ yukon < 9 * kPanBs32Joint ∧ yukon < 12 * kPanBs32Joint := by decide

/-- 12. Exact integer slope threshold: `k · kPanBs32Joint < Yukon ↔ k ≤ 5`. -/
theorem slope_threshold (k : Nat) : k * kPanBs32Joint < yukon ↔ k ≤ 5 := by
  unfold kPanBs32Joint linear perTx blockJoint yukon; omega

/-- 13. Same threshold for the unconditional sum. -/
theorem slope_threshold_sum (k : Nat) : k * kPanBs32Sum < yukon ↔ k ≤ 5 := by
  unfold kPanBs32Sum linear perTx yukon; omega

end InitECandidate.Solver.GuestBs32BlockStorageEnvelope
