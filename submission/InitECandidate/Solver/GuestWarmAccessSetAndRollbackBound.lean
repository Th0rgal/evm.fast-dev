import InitECandidate.Solver.GuestDistinctDeleteOrCallCycleSixSlope

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound`

Hand transcription of `guest.pp.pnk` (wt-2).

* `ev+168` (addresses, 20-byte keys) and `ev+176` (storage, 52-byte `addr‖key` via `sk_make`)
  are ordinary `htab`s, **not** among the 9 `bs+*`/`ts+*` tables. Built per tx from the access list
  (`aa`, `ak`); shared by every frame: `child_message` (l.8668) passes the parent's pointers,
  frame init (l.6909–6914) stores them and records `ev+264/272 = htab_count`.
* `is_warm_address` (l.6934) / `warm_address` (l.6938): `htab_has` / `htab_set` on `ev+168`;
  `is_warm_storage_key` (l.7472) / `warm_storage_key` (l.7479): same on `ev+176`.
* `rollback_child_access` (l.8639): `htab_truncate(ev+168, n₁)`, `htab_truncate(ev+176, n₂)`:
  one `htab_del` per entry added by the reverted child.

Accounting:
* Probes on `ev+176` are already the `is_warm_storage_key` find of `GuestSstoreWarmCoeffAudit`
  (local per-tx cluster): absorbed.
* `ev+176` truncation: `5 · 7,989 · 95,238 = 3,804,281,910`, already in `kPanAccessCall`.
* **`ev+168` truncation is new**: each entry costs ≥ 3,000 gas (30 units) in this Guest; per tx
  `|ev+168| ≤ ⌊167,772/30⌋ + 19 = 5,611` (sender + 18 precompiles), per block ≤ `66,666` deletes:
  `≤ 5 · 5,611 · 66,666 = 1,870,314,630`.
* Address probes `is_warm_address` on `ev+168`: per-tx cluster ≤ 5,611, a warm probe costs
  ≥ 100 gas, bounded by `2 · 5,611` per unit — the same order as the address-table terms already
  absorbed in `12 A²`; not recounted separately here.

`kPanWarmSets = kPanAccessCall + 1,870,314,630 = 161,763,589,338`: `5×` passes, `6×` fails.
-/

namespace InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound

open InitECandidate.Solver.GuestAccessListAndCallStackDominance (kPanAccessCall)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Abstract warm set: size, and the size recorded at child entry. -/
structure Frame where
  size : Nat
  mark : Nat

/-- Child entry: record `htab_count`. -/
def enter (n : Nat) : Frame := ⟨n, n⟩
/-- Warming a new entry. -/
def warm (f : Frame) : Frame := ⟨f.size + 1, f.mark⟩
/-- `htab_truncate(t, mark)`: number of `htab_del` calls. -/
def truncDels (f : Frame) : Nat := f.size - f.mark

/-- `k` warmings in the child. -/
def warmN (f : Frame) (k : Nat) : Frame := ⟨f.size + k, f.mark⟩

/-- 1. Truncation deletes exactly the entries added by the child. -/
theorem trunc_exact (n k : Nat) : truncDels (warmN (enter n) k) = k := by
  simp [truncDels, warmN, enter]

/-- 2. Parent entries survive: after truncation the size is back to the mark. -/
theorem trunc_keeps_parent (n k : Nat) :
    (warmN (enter n) k).size - truncDels (warmN (enter n) k) = n := by
  rw [trunc_exact]; simp [warmN, enter]

/-- 3. Cold address access is 3,000 gas in this Guest (30 units) ≥ the 26 modelled. -/
theorem cold_addr_units : 3000 = 30 * 100 ∧ 26 ≤ 30 := by decide

/-- 4. Per-tx `ev+168` size under EIP-7825: `≤ 5,611`, tight. -/
theorem addr_set_tx (a : Nat) (h : 30 * a ≤ 167772) : a + 19 ≤ 5611 := by omega

theorem addr_set_tx_tight : 30 * 5592 ≤ 167772 ∧ 167772 < 30 * 5593 := by decide

/-- 5. Per-block deleted address entries: `≤ 66,666`, tight. -/
theorem addr_dels_block (n : Nat) (h : 30 * n ≤ 2000000) : n ≤ 66666 := by omega

/-- Truncation ticks: `n` deletes on clusters of size ≤ `a` cost `≤ 5 a` each. -/
def truncTicks (a n : Nat) : Nat := 5 * a * n

/-- 6. `ev+168` truncation bound. -/
theorem addr_trunc_le (a n : Nat) (ha : a ≤ 5611) (hn : n ≤ 66666) :
    truncTicks a n ≤ 1870314630 := by
  unfold truncTicks
  have : a * n ≤ 5611 * 66666 := Nat.mul_le_mul ha hn
  calc 5 * a * n = 5 * (a * n) := by ring
    _ ≤ 5 * (5611 * 66666) := by omega
    _ = 1870314630 := by decide

/-- 7. Tight at the corner. -/
theorem addr_trunc_tight : truncTicks 5611 66666 = 1870314630 := by decide

/-- 8. Storage-set truncation is already the `3,804,281,910` term of `kPanAccessCall`. -/
theorem storage_trunc_in_access : kPanAccessCall = 136116135658 + 19972857140 + 3804281910 := by decide

/-- New envelope with both warm sets. -/
def kPanWarmSets : Nat := kPanAccessCall + 1870314630

/-- 9. Value. -/
theorem kPanWarmSets_val : kPanWarmSets = 161763589338 := by decide

/-- 10. `5×` passes with margin `91,901,978,784`; `6×` fails. -/
theorem slopes :
    5 * kPanWarmSets < yukon ∧ yukon - 5 * kPanWarmSets = 91901978784 ∧ yukon < 6 * kPanWarmSets := by
  decide

end InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound
