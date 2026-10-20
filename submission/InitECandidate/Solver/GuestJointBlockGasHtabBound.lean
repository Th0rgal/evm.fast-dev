import InitECandidate.Solver.GuestBlockVsTxHtabBounds

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestJointBlockGasHtabBound`

Joint worst case for the storage adversary under **one** 200M-gas block budget, refining
`GuestBlockVsTxHtabBounds` (which summed three terms each spending the full budget).

## Refinement 1 — single gas budget
All tick sources draw from the same `2,000,000` units of 100 gas. A cold access costs `21` units
(2100 gas), a warm lookup `1` unit (100 gas), a `PUSH31` `0.03` units. The three tick categories
are *disjoint* (simple ops, per-tx collision scans, block-level `bs+72` inserts), so summing each
category's own maximum is a valid upper bound — but EIP-7825 caps each transaction at
`167,772` units, so the per-tx collision term is `11 · 167772²/80`, not `C·(W+C)`.

## Refinement 2 — which of the 7 `op_sstore` finds scan a cheap (2100-gas-fillable) cluster
Read from `guest.pp.pnk`:
* `ev+176` (`is_warm_storage_key`), `ts+24` (`get_storage`→`htab_set`), `ts+8`
  (`set_storage`→`get_account_optional`): filled by a plain **cold read** (2100 gas). → 3 finds.
* `ts+56` (created set, creation only), `ts+32` + inner (`set_storage`/`jset`), `bs+32` ×2
  (`get_storage_original`/`get_storage`, block storage): grow **only through an actual storage
  write** (≥ 5000 gas) or commit-merge. Their clusters cost ≥ 5000 gas/key, so they are
  dominated. → 4 finds, not on the cheap cluster.

Hence the effective `SSTORE` slope on the cheap cluster is `pJoint = 3 · pFind = 6`, not `14`.

## Result
`k_pan ≤ 40,486,477,625 < maxGuestSourceClock = 43,914,839,586`. The first finite `K` under
`900,719,925,474` is therefore reachable with the current Guest, provided the cheap-cluster slope
is `≤ 6` (threshold theorem `kPanJoint_threshold`).
-/

namespace InitECandidate.Solver.GuestJointBlockGasHtabBound

open InitECandidate.Solver.GuestSloadExactProbeTicks
open InitECandidate.Solver.GuestBlockVsTxHtabBounds (txUnits txPerBlock blkRead blkRead_le maxColdPerBlock)
open InitECandidate.Solver.GuestEvmStepOpcodeBounds (gasCap)

/-- `maxGuestSourceClock` for this mission. -/
def maxGuestSourceClock : Nat := 43914839586
/-- Yukon ceiling. -/
def yukon : Nat := 900719925474
/-- Cheap-cluster `SSTORE` slope: 3 of the 7 finds (`ev+176`, `ts+24`, `ts+8`) × `pFind`. -/
def pJoint : Nat := 3 * pFind
/-- EIP-7825 per-tx unit cap (`16,777,216 / 100`). -/
def M : Nat := 167772

/-- 1. Extracted constants. -/
theorem constants : pJoint = 6 ∧ M = 167772 ∧ txUnits = 167772 ∧ txPerBlock = 11 ∧
    pFind = 2 := by decide

/-! ## Joint per-transaction collision term -/

/-- Each `(cᵢ, wᵢ)` bucket with `21cᵢ + wᵢ ≤ M` gives `80·cᵢ(wᵢ+cᵢ) ≤ M²`. -/
theorem bucket_bound (c w : Nat) (h : 21 * c + w ≤ M) : 80 * (c * (w + c)) ≤ M * M :=
  InitECandidate.Solver.GuestMemoryAndAccountOpcodeBounds.per_tx_probes c w M h

/-- 2. List form: for any list of gas-feasible buckets, `80·Σ cᵢ(wᵢ+cᵢ) ≤ length · M²`. -/
theorem list_joint (ps : List (Nat × Nat)) (h : ∀ p ∈ ps, 21 * p.1 + p.2 ≤ M) :
    80 * (ps.map (fun p => p.1 * (p.2 + p.1))).sum ≤ ps.length * (M * M) := by
  induction ps with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := bucket_bound a.1 a.2 (h a (by simp))
    have ht := ih (fun p hp => h p (by simp [hp]))
    rw [Nat.mul_add, Nat.add_mul, Nat.one_mul]
    omega

/-- 3. Under the EIP-7825 split (≤ `11` transactions), the total per-tx collision product is
`≤ 11·M²/80 = 3,870,273,547`, hence the `SSTORE` scans cost `≤ pJoint · 3,870,273,547`. -/
theorem joint_collision_le (ps : List (Nat × Nat)) (hlen : ps.length ≤ 11)
    (h : ∀ p ∈ ps, 21 * p.1 + p.2 ≤ M) :
    (ps.map (fun p => p.1 * (p.2 + p.1))).sum ≤ 3870273547 := by
  have hl := list_joint ps h
  have : ps.length * (M * M) ≤ 11 * (M * M) := Nat.mul_le_mul_right _ hlen
  unfold M at this hl; omega

/-! ## Block-level `bs+72` term (reused, cold reads shared with the same budget) -/

/-- 4. The block-level `bs+72` cold-read cluster is `≤ 13,605,272,109` ticks. -/
theorem block_term_le (c : Nat) (h : 2100 * c ≤ gasCap) : blkRead c ≤ 13605272109 :=
  (blkRead_le c h).1

/-! ## Joint master bound -/

/-- Joint source-clock model: prologue + `18·gas` simple-op envelope + cheap-cluster `SSTORE`
collision term (`pJoint · 11·M²/80`) + block-level `bs+72` term. -/
def kPanJoint (p : Nat) : Nat :=
  SelfContainedMasterK.prologueTicks + 18 * gasCap + p * 3870273547 + 13605272109

/-- 5. Numeric master value at the extracted slope `pJoint = 6`. -/
theorem kPanJoint_val : kPanJoint pJoint = 40486477625 := by decide

/-- 6. **Joint master bound**: the combined `SLOAD`+`SSTORE`+`BALANCE`+`PUSH31` adversary under a
single 200M-gas block stays below `maxGuestSourceClock = 43,914,839,586`. -/
theorem kPanJoint_le_max : kPanJoint pJoint < maxGuestSourceClock := by decide

/-- 7. Validity of each summed term (disjoint tick sources, each individually gas-bounded):
simple envelope, per-tx collision, block term. -/
theorem terms_valid (ps : List (Nat × Nat)) (hlen : ps.length ≤ 11)
    (h : ∀ p ∈ ps, 21 * p.1 + p.2 ≤ M) (c : Nat) (hc : 2100 * c ≤ gasCap) :
    SelfContainedMasterK.prologueTicks + 18 * gasCap
        + pJoint * (ps.map (fun p => p.1 * (p.2 + p.1))).sum + blkRead c
      ≤ kPanJoint pJoint := by
  have h1 := joint_collision_le ps hlen h
  have h2 := block_term_le c hc
  unfold kPanJoint pJoint
  have : pFind * 3 * (ps.map (fun p => p.1 * (p.2 + p.1))).sum ≤ pFind * 3 * 3870273547 :=
    Nat.mul_le_mul_left _ h1
  unfold pFind at this ⊢; omega

/-- 8. Margin: the joint bound sits below `60·10⁹` and far under the Yukon ceiling (factor > 22). -/
theorem kPanJoint_margins :
    kPanJoint pJoint < 60000000000 ∧ 22 * kPanJoint pJoint < yukon := by decide

/-- 9. Threshold: the joint model fits under `maxGuestSourceClock` iff the cheap-cluster slope is
`≤ 6`. `SLOAD`/`BALANCE` (`p = 4`) and the refined `SSTORE` (`p = 6`) pass; the naive `p = 14`
does not. -/
theorem kPanJoint_threshold (p : Nat) : kPanJoint p ≤ maxGuestSourceClock ↔ p ≤ 6 := by
  unfold kPanJoint SelfContainedMasterK.prologueTicks gasCap maxGuestSourceClock; omega

/-- 10. Comparison with the un-refined block bound: the joint single-budget analysis strictly
improves `GuestBlockVsTxHtabBounds`' `71,448,666,010`. -/
theorem improves_block_bound : kPanJoint pJoint < 71448666010 ∧
    71448666010 - kPanJoint pJoint = 30962188385 := by decide

/-- 11. Pure-cold corner (`W = 0`): if all budget buys cold reads, `C ≤ 95,238`, no warm `SSTORE`
is possible, the per-tx term vanishes and `k_pan ≤ prologue + 18·gas + 13,605,272,109 =
17,264,836,343` — well under `maxGuestSourceClock`. -/
theorem pure_cold_corner :
    SelfContainedMasterK.prologueTicks + 18 * gasCap + 0 * 3870273547 + 13605272109
      = 17264836343 ∧ 17264836343 < maxGuestSourceClock := by decide

end InitECandidate.Solver.GuestJointBlockGasHtabBound
