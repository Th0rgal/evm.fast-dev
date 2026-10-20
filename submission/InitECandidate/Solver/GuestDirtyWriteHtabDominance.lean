import InitECandidate.Solver.GuestJointBlockGasHtabBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestDirtyWriteHtabDominance`

1. The dirty-write quadratic bound `50d + w ≤ m ⇒ 196·d·(w+d) ≤ m²` holds and is tight.
2. **But its premise does not apply to the Guest.** In `guest.pp.pnk`, `op_sstore` (l.7499) calls
   `set_storage(target, key, new_value)` unconditionally, even when `new_value = current` (no-op).
   `set_storage` (l.5767) does `jset(inner, key, v)`, inserting the key into `ts+32`'s inner table,
   and `merge_tx_into_block` (l.5911) unions every `ts+32` inner table into `bs+32`. So a **cold
   no-op `SSTORE` (2100 gas = 21 units, stipend check only)** inserts into `ts+32` and, after commit,
   into the block table `bs+32`. These tables are filled at 21 units/key, not ≥ 50.
3. Consequence: a `bs+32` inner cluster of `D` colliding keys for one address persists across
   transactions. Each later warm `SLOAD` of a colliding key absent from `ts+32` misses in
   `stor_lookup(bs+32)` and scans the whole cluster (≥ 2 ticks/slot). With `21·D + W ≤ 2·10⁶`,
   this block-level term reaches `2·47,619,047,619 = 95,238,095,238` ticks, above
   `maxGuestSourceClock` and outside the per-tx EIP-7825 split. So `kPanJoint 6` is **not** an
   upper bound for the current Guest, and refinement 2 of `GuestJointBlockGasHtabBound` (3 of 7
   finds cheap) is wrong for `ts+32`/`bs+32`.
-/

namespace InitECandidate.Solver.GuestDirtyWriteHtabDominance

open InitECandidate.Solver.GuestJointBlockGasHtabBound (kPanJoint pJoint maxGuestSourceClock yukon)
open InitECandidate.Solver.HtabQuadraticCollisionMax (cw_le_cold)

/-- 1. Completion of the square for dirty writes: `50d + w ≤ m ⇒ 196·d·(w+d) ≤ m²`. -/
theorem dirty_square (d w m : Nat) (h : 50 * d + w ≤ m) : 196 * (d * (w + d)) ≤ m * m := by
  have hb : (w : Int) + d ≤ m - 49 * d := by omega
  have hd : (0 : Int) ≤ d := by omega
  have hmul : (d : Int) * (w + d) ≤ d * (m - 49 * d) := Int.mul_le_mul_of_nonneg_left hb hd
  have hsq : (0 : Int) ≤ ((m : Int) - 98 * d) ^ 2 := sq_nonneg _
  have : (196 : Int) * (d * (w + d)) ≤ m * m := by nlinarith
  exact_mod_cast this

/-- 2. Tightness at `(d, w, m) = (200, 9600, 19600)`. -/
theorem dirty_square_tight : 50 * 200 + 9600 = 19600 ∧ 196 * (200 * (9600 + 200)) = 19600 * 19600 := by
  decide

/-- 3. `22,100`-gas writes (221 units): `221d + w ≤ m ⇒ 880·d·(w+d) ≤ m²`. -/
theorem cold_write_square (d w m : Nat) (h : 221 * d + w ≤ m) : 880 * (d * (w + d)) ≤ m * m := by
  have hb : (w : Int) + d ≤ m - 220 * d := by omega
  have hd : (0 : Int) ≤ d := by omega
  have hmul : (d : Int) * (w + d) ≤ d * (m - 220 * d) := Int.mul_le_mul_of_nonneg_left hb hd
  have hsq : (0 : Int) ≤ ((m : Int) - 440 * d) ^ 2 := sq_nonneg _
  have : (880 : Int) * (d * (w + d)) ≤ m * m := by nlinarith
  exact_mod_cast this

/-- 4. Under the dirty premise, the per-probe ratio is strictly smaller: `8/196 < 6/80`. -/
theorem dirty_ratio_lt : 8 * 80 < 6 * 196 := by decide

/-- 5. Correction of the requested block arithmetic: `8·(2·10⁶)²/196 = 163,265,306,120`, not
`16,326,530,612`; even under the dirty premise this block term exceeds `maxGuestSourceClock`. -/
theorem dirty_block_term :
    8 * (2000000 * 2000000 / 196) = 163265306120 ∧
      maxGuestSourceClock < 8 * (2000000 * 2000000 / 196) := by decide

/-! ## Actual Guest: `bs+32` is filled by cold no-op `SSTORE`s at 21 units/key -/

/-- Cost in 100-gas units of a cold no-op `SSTORE` that inserts into `ts+32` (→ `bs+32` at commit). -/
def noopColdUnits : Nat := 21
/-- Ticks per slot scanned by `stor_lookup(bs+32)` (loop iteration + `memeq`). -/
def pBs32 : Nat := 2

/-- 6. Block-level `bs+32` cluster term under the true 21-unit fill cost: for `21·D + W ≤ 2·10⁶`,
`pBs32·D·W ≤ 95,238,095,238`. -/
theorem bs32_term_le (D W : Nat) (h : noopColdUnits * D + W ≤ 2000000) :
    pBs32 * (D * W) ≤ 95238095238 := by
  have := cw_le_cold D W h
  unfold pBs32; omega

/-- 7. Attained at `(D, W) = (47,619, 1,000,001)`, exactly 200M gas. -/
theorem bs32_term_tight :
    noopColdUnits * 47619 + 1000001 = 2000000 ∧ pBs32 * (47619 * 1000001) = 95238095238 := by
  decide

/-- 8. The `bs+32` term alone exceeds both `maxGuestSourceClock` and `kPanJoint 6`: the joint
envelope does not dominate the dirty tables in the current Guest. -/
theorem bs32_breaks_joint :
    maxGuestSourceClock < pBs32 * (47619 * 1000001) ∧
      kPanJoint pJoint < pBs32 * (47619 * 1000001) := by decide

/-- 9. It stays under the Yukon ceiling with factor > 9. -/
theorem bs32_within_yukon : 9 * (pBs32 * (47619 * 1000001)) < yukon := by decide

/-- 10. Threshold: a `bs+32` fill cost of `u` units/key keeps `2·D·W` under `maxGuestSourceClock`
only if `u ≥ 46` at the balanced point: `2·D·(2·10⁶ − u·D)` with `D = 10⁶/u`. Witness: `u = 21`
fails, `u = 46` passes. -/
theorem fill_cost_threshold :
    maxGuestSourceClock < 2 * ((1000000 / 21) * (2000000 - 21 * (1000000 / 21))) ∧
      2 * ((1000000 / 46) * (2000000 - 46 * (1000000 / 46))) < maxGuestSourceClock := by decide

end InitECandidate.Solver.GuestDirtyWriteHtabDominance
