import InitECandidate.Solver.GuestStateRestoreCoupledTightening

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes`

Hand transcription of `guest.pp.pnk` (wt-2).

* Tx loop (l.15001 → 15016, l.15375 → 15388): `incorporate_tx_into_block` (→ `merge_tx_into_block`,
  l.5911) is followed by `state_fresh_tx` (l.5419), which allocates fresh `ts+8..ts+64` tables.
* Hence at any instant `ts+32` holds only current-tx keys (`D_x`) and `bs+32` only earlier-tx keys
  (`D_b`), with `21(D_b + D_x) + W ≤ S`.

Effect: one warm `SSTORE` no-op + restore costs `≤ 2·D_b` (block probes) `+ 13·D_x` (tx probes +
`htab_del`). Under the partition this is `≤ 13·(D_b + D_x)` — but the earlier envelopes already
priced the two terms on **separate** sizes: `bs+32` on the prefix (`100 G` merge envelope) and
`ts+32` on the per-tx local `d` (`13 · 3,994,571,428`, EIP-7825 tx cap). The partition is
exactly the structure they assumed, so it gives no slack: `kPanDisjointTables = kPanAccessCall`.
Both terms peak at different splits (block term: one big key set across txs; local term: keys
re-created in each tx), and the sum of maxima is not attained jointly, but no tighter joint bound
is proved here. `6×` still fails.
-/

namespace InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes

open InitECandidate.Solver.GuestAccessListAndCallStackDominance (kPanAccessCall)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Abstract per-tx state: `(D_b, D_x)` sizes of `bs+32`, `ts+32`. -/
structure Sizes where
  db : Nat
  dx : Nat

/-- `merge_tx_into_block` then `state_fresh_tx`: `ts+32` folded into `bs+32`, then reset. -/
def endTx (s : Sizes) : Sizes := ⟨s.db + s.dx, 0⟩

/-- A first dirty write in the current tx. -/
def dirty (s : Sizes) : Sizes := ⟨s.db, s.dx + 1⟩

/-- 1. The total `D_b + D_x` is preserved by the end-of-tx merge/reset. -/
theorem endTx_total (s : Sizes) : (endTx s).db + (endTx s).dx = s.db + s.dx := by
  simp [endTx]

/-- 2. After the reset `ts+32` is empty. -/
theorem endTx_fresh (s : Sizes) : (endTx s).dx = 0 := rfl

/-- 3. Each dirty write adds exactly one to the total. -/
theorem dirty_total (s : Sizes) : (dirty s).db + (dirty s).dx = s.db + s.dx + 1 := by
  simp [dirty]; omega

/-- 4. Partition invariant: if `D` cold dirty writes are paid (`21 D + W ≤ S`), `D_b + D_x ≤ D`
and the gas constraint holds on `(D_b, D_x)`. -/
theorem partition (db dx D W : Nat) (hp : db + dx ≤ D) (h : 21 * D + W ≤ 2000000) :
    21 * (db + dx) + W ≤ 2000000 := by omega

/-- Ticks of one warm no-op `SSTORE` + its `state_restore` against sizes `(D_b, D_x)`. -/
def cycleTicks (db dx : Nat) : Nat := 2 * db + 13 * dx

/-- 5. Under the partition, the cycle is `≤ 13·D`. -/
theorem cycle_le (db dx D : Nat) (hp : db + dx ≤ D) : cycleTicks db dx ≤ 13 * D := by
  unfold cycleTicks; omega

/-- 6. Tight: all keys in the current tx (`D_b = 0`). -/
theorem cycle_tight (D : Nat) : cycleTicks 0 D = 13 * D := by unfold cycleTicks; omega

/-- 7. All keys merged into the block (`D_x = 0`): only `2·D`. -/
theorem cycle_block_only (D : Nat) : cycleTicks D 0 = 2 * D := by unfold cycleTicks; omega

/-- 8. Exchange: moving a key from `ts+32` to `bs+32` lowers the cycle by `11`. -/
theorem cycle_exchange (db dx : Nat) : cycleTicks (db + 1) dx + 11 = cycleTicks db (dx + 1) := by
  unfold cycleTicks; omega

/-- 9. The partition gives no new slack: the clock is unchanged. -/
def kPanDisjointTables : Nat := kPanAccessCall

theorem kPanDisjoint_val : kPanDisjointTables = 159893274708 := by decide

/-- 10. `5×` passes, `6×` fails; margin at `5×`. -/
theorem slopes :
    5 * kPanDisjointTables < yukon ∧ yukon < 6 * kPanDisjointTables ∧
      yukon - 5 * kPanDisjointTables = 101253551934 := by decide

end InitECandidate.Solver.GuestDisjointBlockAndTxTableSizes
