import InitECandidate.Solver.HtabQuadraticCollisionMax

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.GuestSloadExactProbeTicks`

Probe costs read off `Guest/guest.pp.pnk` (hand transcription, `PanSem` clock rules:
1 tick per executed `while` body, 1 per `.call`, 0 otherwise):

* `htab_find_slot` (l.1588): per occupied probed slot, 1 loop iteration + 1 `memeq` call.
  `memeq` on 32/52-byte keys from aligned buffers (`sk_buf = alloc(64)`, `evm_key_buf =
  alloc(32)`) takes the unrolled fast path, no loop ⇒ `pFind = 2`.
* `htab_insert_raw` (l.1619): 1 loop iteration per occupied slot, no call ⇒ `pIns = 1`.
* `op_sload` (l.7482) warm: `is_warm_storage_key` (find in `ev+176`, 52-byte keys) and
  `get_storage` → `htab_set(ts+24)` (find, 52-byte keys) ⇒ 2 colliding finds per lookup.
  `stor_lookup` on `ts+32`/`bs+32` only touches keys previously `SSTORE`d (none in an
  `SLOAD`-only attack); `ws_get_storage` walks the trie, not a `htab`.
* `op_sload` cold: miss-find in `ev+176`, `warm_storage_key` = `htab_set(ev+176)` (miss-find +
  insert), `get_storage` = `htab_set(ts+24)` (miss-find + insert).

Collision note: `htab_hash` XORs 8-byte little-endian lanes, so byte `i` of the storage key
lands in lane `i mod 8` (32-byte key) and lane `(i+20) mod 8` (52-byte `addr‖key`). Any byte
permutation preserving `i mod 8` collides in every table at once.
-/

namespace InitECandidate.Solver.GuestSloadExactProbeTicks

open InitECandidate.Solver.HtabQuadraticCollisionMax

/-- Ticks per occupied slot visited by `htab_find_slot`. -/
def pFind : Nat := 2
/-- Ticks per occupied slot visited by `htab_insert_raw`. -/
def pIns : Nat := 1
/-- Colliding tables searched by a warm `SLOAD`. -/
def warmTables : Nat := 2

/-- Quadratic ticks of a warm `SLOAD` on a cluster of `c` keys (all slots probed). -/
def warmProbeTicks (c : Nat) : Nat := warmTables * pFind * c
/-- Quadratic ticks of the cold `SLOAD` inserting the `(j+1)`-th colliding key on `j` keys:
3 miss-finds + 2 inserts. -/
def coldProbeTicks (j : Nat) : Nat := (3 * pFind + 2 * pIns) * j
/-- Sum over `c` successive cold inserts. -/
def coldTotal : Nat → Nat
  | 0 => 0
  | c + 1 => coldTotal c + coldProbeTicks c

/-- Effective per-probe slope `p` for the `HtabQuadraticCollisionMax` model. -/
def pEff : Nat := warmTables * pFind

/-- 1. Extracted constants. -/
theorem constants : pFind = 2 ∧ pIns = 1 ∧ warmTables = 2 ∧ pEff = 4 := by decide

/-- 2. Warm `SLOAD` costs exactly `4c` probe ticks. -/
theorem warm_eq (c : Nat) : warmProbeTicks c = 4 * c := by
  unfold warmProbeTicks warmTables pFind; omega

/-- 3. A cold insert on `j` colliding keys costs exactly `8j` probe ticks. -/
theorem cold_eq (j : Nat) : coldProbeTicks j = 8 * j := by
  unfold coldProbeTicks pFind pIns; omega

/-- 4. Closed form: `c` cold inserts cost `4·c·(c−1)` probe ticks. -/
theorem coldTotal_eq (c : Nat) : coldTotal c = 4 * (c * (c - 1)) := by
  induction c with
  | zero => rfl
  | succ n ih =>
    rw [coldTotal, ih, cold_eq]
    cases n with
    | zero => rfl
    | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.add_mul (m + 1) 1 (m + 1), Nat.mul_comm (m + 1) m, Nat.add_mul m 1 (m + 1)]
      omega

/-- 5. Total collision ticks of the schedule are bounded by `pEff · c · (w + c)`. -/
theorem schedule_le_model (c w : Nat) :
    coldTotal c + w * warmProbeTicks c ≤ pEff * (c * (w + c)) := by
  rw [coldTotal_eq, warm_eq]
  unfold pEff warmTables pFind
  have : c * (c - 1) ≤ c * c := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  rw [Nat.mul_add c w c]
  have h : w * (4 * c) = 4 * (c * w) := by rw [Nat.mul_comm w, Nat.mul_assoc, Nat.mul_comm c]
  omega

/-- 6. Under 200M gas (access-list pricing, the cheapest) the collision ticks are
`≤ 222,222,222,208`. -/
theorem schedule_le (c w : Nat) (h : 19 * c + w ≤ 2000000) :
    coldTotal c + w * warmProbeTicks c ≤ 222222222208 := by
  have := schedule_le_model c w
  have hp := probes_le c w h
  unfold pEff warmTables pFind at this; omega

/-- 7. Instantiated source clock: `k_pan ≤ 225,881,786,442`, tight at `(55,556, 944,436)`. -/
theorem kPan_extracted (c w : Nat) (h : 19 * c + w ≤ 2000000) :
    kPanModel pEff c w ≤ 225881786442 ∧ kPanModel pEff 55556 944436 = 225881786442 := by
  have hp := probes_le c w h
  refine ⟨?_, by decide⟩
  unfold kPanModel pEff warmTables pFind SelfContainedMasterK.prologueTicks
    GuestEvmStepOpcodeBounds.gasCap
  omega

/-- 8. Position w.r.t. the two ceilings: above `maxGuestSourceClock`, below Yukon `900,719,925,474`
with margin factor `> 3`. -/
theorem kPan_extracted_ceilings :
    GuestEvmStepOpcodeBounds.maxGuestSourceClock < kPanModel pEff 55556 944436 ∧
      3 * kPanModel pEff 55556 944436 < 900719925474 ∧
      4 * kPanModel pEff 55556 944436 > 900719925474 := by decide

/-- 9. Concrete pure-`SLOAD` cold-key schedule `(47,619, 1,000,001)` (2100 gas cold):
collision ticks `= 199,546,276,644`. -/
theorem cold_schedule_exact :
    coldTotal 47619 + 1000001 * warmProbeTicks 47619 = 199546276644 := by
  rw [coldTotal_eq, warm_eq]

/-- 10. Margin: `pEff = 4 ≤ 16`, so the Yukon ceiling holds for the extracted slope. -/
theorem pEff_within_yukon : kPanModel pEff 55556 944436 < 900719925474 ↔ pEff ≤ 16 :=
  (kPan_general pEff).2

end InitECandidate.Solver.GuestSloadExactProbeTicks
