import InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope`

Hand transcription of `guest.pp.pnk` (wt-2).

* `jset` (l.5441) journals `present = (htab_get(t, key)).0`; `state_restore` (l.5481) deletes only
  when `present = false`. After the first `jset` in a frame the key is in `ts+32`, so a second
  `SSTORE` on it inside the same child journals `present = true` (restore by `htab_set`).
* Warm storage set is `ev+176` (`is_warm_storage_key` l.7472), built per tx; warming a new key
  costs ≥ 19 units (access list) or 21 (cold `SLOAD`/`SSTORE`).
* `op_call` (l.8855) / `op_staticcall` (l.9039): `access_cost = 100` warm (3000 cold), charged
  before the call; `SSTORE` warm no-op: 100 gas.

**Conditional module.** Premise `H2` (not enforced by the code): each `htab_del` on `ts+32` is paid by either a fresh warm key (≥ 19 + 1 units) or a new
`CALL` + `SSTORE` + `REVERT` cycle (≥ 2 units). With the upstream local coefficient `8` per
warm op per unit, a delete op costs `8d + 5d = 13d` ticks for ≥ 2 units, i.e. ≤ `6.5d` per unit
< `8d`: deletes never beat plain warm ops. The revert surcharge `5 · 3,994,571,428` vanishes, and
`kPanSixSlopeRestored = kPanUnifiedAllTables + 3,804,281,910 = 139,920,417,568`.
Counter to `H2`: after `REVERT` the keys leave `ts+32` but stay in the parent's `ev+176`, so a
child can re-`SSTORE` the same `K` warm keys every cycle: `K` deletes for `K + c₀` units, i.e.
`1 + c₀/K` units per delete. `H2` holds only if `K ≤ c₀`. Without `H2`, `kPanAccessCall` stands.
The `CALL` frame overhead itself is assumed linear (inside 18 ticks/gas), not recounted.
-/

namespace InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope

open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope (kPanUnifiedAllTables)
open InitECandidate.Solver.GuestAccessListAndCallStackDominance (kPanAccessCall)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Journal flags of a sequence of `SSTORE`s inside one child frame, starting from the set of keys
already in `ts+32`: `present` is membership at `jset` time; `jset` then inserts the key. -/
def journalFlags : List Nat → List Nat → List Bool
  | _, [] => []
  | tbl, k :: ks => (k ∈ tbl) :: journalFlags (k :: tbl) ks

/-- Number of `htab_del` restores (flags `false`). -/
def dels (tbl ks : List Nat) : Nat := (journalFlags tbl ks).count false

/-- 1. A repeated key in the same frame is journaled as present (no delete). -/
theorem repeat_no_delete (k : Nat) : journalFlags [] [k, k] = [false, true] := by
  simp [journalFlags]

/-- 2. Deletes count distinct new keys only: `[1,1,1,2,2]` from an empty `ts+32` gives 2 deletes,
and a key already in `ts+32` gives none. -/
theorem dels_distinct : dels [] [1, 1, 1, 2, 2] = 2 ∧ dels [1] [1, 1] = 0 := by decide

/-- Gas (100-gas units) of a delete realised by a CALL cycle: CALL (100) + SSTORE (100). -/
def cycleUnits : Nat := 2
/-- Gas of a delete realised by a fresh key: warm (≥ 19) + SSTORE (1). -/
def freshUnits : Nat := 20

/-- 3. `op_call` warm access and warm `SSTORE` are 100 gas each: a cycle is ≥ 2 units. -/
theorem cycle_units : 100 + 100 = cycleUnits * 100 ∧ 19 * 100 + 100 = freshUnits * 100 := by decide

/-- 4. **Per-unit dominance**: a delete op (`13 d` ticks) on ≥ 2 units costs ≤ `8 d` per unit. -/
theorem delete_per_unit (d u : Nat) (hu : cycleUnits ≤ u) : 13 * d ≤ 8 * d * u := by
  unfold cycleUnits at hu; nlinarith

/-- 5. Same with a fresh-key delete (≥ 20 units). -/
theorem fresh_per_unit (d u : Nat) (hu : freshUnits ≤ u) : 13 * d ≤ 8 * d * u := by
  unfold freshUnits at hu; nlinarith

/-- 6. Any mix of `p` plain warm ops (1 unit, `8d`) and `q` delete ops (≥ 2 units, `13d`) under
`p + 2q ≤ w` costs ≤ `8 d w`: the revert surcharge is absorbed in the upstream local term. -/
theorem revert_le_tight (d p q w : Nat) (h : p + cycleUnits * q ≤ w) :
    8 * d * p + 13 * d * q ≤ 8 * d * w := by
  unfold cycleUnits at h; nlinarith [Nat.zero_le (d * q)]

/-- 7. Tight: all plain ops reach `8 d w`. -/
theorem revert_tight (d w : Nat) : 8 * d * w + 13 * d * 0 = 8 * d * w := by ring

/-- 8. The old per-unit delete cost `13 d` per **1** unit is no longer reachable: strict drop. -/
theorem strict_drop : 13 * 1 * 1 > 8 * 1 * 1 ∧ 13 * 1 ≤ 8 * 1 * cycleUnits := by decide

/-- Restored envelope: unified tables + warm-set truncation; no revert surcharge. -/
def kPanSixSlopeRestored : Nat := kPanUnifiedAllTables + 3804281910

/-- 9. Value and gain over `kPanAccessCall` (exactly the `5 · 3,994,571,428` surcharge). -/
theorem kPan_val : kPanSixSlopeRestored = 139920417568 ∧
    kPanAccessCall - kPanSixSlopeRestored = 19972857140 ∧ kPanSixSlopeRestored < 150119987579 := by
  decide

/-- 10. **`6×` back under Yukon**, `7×` not. -/
theorem six_slope :
    6 * kPanSixSlopeRestored < yukon ∧ yukon - 6 * kPanSixSlopeRestored = 61197420066 ∧
      yukon < 7 * kPanSixSlopeRestored := by decide

end InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope
