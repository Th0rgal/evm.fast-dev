import InitECandidate.Solver.GuestAccessListAndCallStackDominance

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestStateRestoreCoupledTightening`

Hand transcription of `guest.pp.pnk` (wt-2). **Negative result**: the proposed tightening
("`htab_del` only for first writes costing ≥ 20 units") is false in this Guest.

Code facts:
* `jset` (l.5441): records `old = htab_get(t, key)` (present flag `old.0`) **always**, then `htab_set`.
* `state_restore` (l.5481): `old.0 ≠ 0 → htab_set(t, key, old)`, else `htab_del(t, key)`.
* `op_sstore` (l.7499): `gas_cost = access_cost (+10000 iff original = current ≠ new)`;
  a no-op warm `SSTORE` costs **100 gas** and still calls `set_storage → jset(inner, key, v)`.
* `get_storage` (l.5658) only does `htab_set(ts+24)`: a key warmed by `SLOAD` (21 units, once per tx)
  is **not** in `ts+32`.

Attack: warm `K` keys by `SLOAD` (`ev+176`, kept by the parent frame); loop
{`CALL` child; child does `K` no-op `SSTORE`s (100 gas each, each inserts a key absent from
`ts+32`); `REVERT`}. Each child `SSTORE` is journaled with `present = false`, so `state_restore`
calls `htab_del` on it: one `htab_del` per **1-unit** operation (plus the amortised call overhead).
So `htab_del` count is not bounded by `D + R`; the 13-tick local coefficient of
`GuestAccessListAndCallStackDominance` stays, and `kPanStateRestoreCoupled = kPanAccessCall`.
-/

namespace InitECandidate.Solver.GuestStateRestoreCoupledTightening

open InitECandidate.Solver.GuestAccessListAndCallStackDominance (kPanAccessCall)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Restore action chosen by `state_restore` from the journaled `present` flag. -/
inductive Restore | set | del deriving DecidableEq, Repr

def restoreOf (present : Bool) : Restore := if present then .set else .del

/-- `op_sstore` charged gas (no state gas), from `(warm, original = current, current = new)`. -/
def sstoreGas (warm oc cn : Bool) : Nat :=
  (if warm then 100 else 2100) + (if oc && !cn then 10000 else 0)

/-- 1. `state_restore` dispatch: `htab_del` exactly when the key was absent before `jset`. -/
theorem restore_dispatch (p : Bool) : restoreOf p = .del ↔ p = false := by
  cases p <;> decide

/-- 2. A warm no-op `SSTORE` (`current = new`) costs 100 gas, i.e. one 100-gas unit. -/
theorem noop_warm_gas (oc : Bool) : sstoreGas true oc true = 100 := by cases oc <;> decide

/-- 3. Only a value-changing write on a clean slot pays `+10,000`. -/
theorem changing_write_gas : sstoreGas true true false = 10100 ∧ sstoreGas false true false = 12100 := by
  decide

/-- One `SSTORE` on a key: returns (journaled `present`, new table membership). `jset` always
journals, whatever the value. -/
def jsetStep (inTable : Bool) : Bool × Bool := (inTable, true)

/-- 4. A no-op `SSTORE` on a warm key absent from `ts+32` is journaled as `present = false`,
hence restored by `htab_del`, while costing 100 gas. -/
theorem noop_absent_deletes :
    restoreOf (jsetStep false).1 = .del ∧ sstoreGas true true true = 100 := by decide

/-- 5. A rewrite of a key already in `ts+32` is restored by `htab_set` (no shift). -/
theorem rewrite_sets : restoreOf (jsetStep true).1 = .set := by decide

/-- Restores in one child call doing `k` `SSTORE`s on `k` distinct keys absent from `ts+32`. -/
def delsPerCall (k : Nat) : Nat := ((List.replicate k false).map restoreOf).countP (· == .del)

/-- 6. Every one of the `k` child `SSTORE`s produces one `htab_del`. -/
theorem dels_per_call (k : Nat) : delsPerCall k = k := by
  unfold delsPerCall
  induction k with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.countP_cons, restoreOf] at ih ⊢; omega

/-- 7. Units per cycle `k + c₀` (`c₀` = constant call/revert overhead in units) give `k` deletes:
deletes per unit ≥ `k/(k + c₀)`, so `htab_del` count is `Θ(W)`, not `≤ D + R`. -/
theorem dels_vs_units (k c0 n : Nat) :
    n * delsPerCall k + n * c0 = n * (k + c0) := by rw [dels_per_call]; ring

/-- 8. Concrete counterexample to "`#htab_del ≤ D + R`": with `D = R = 0`, 1,000 cycles of
`k = 100` deletes give `100,000` deletes. -/
theorem del_bound_refuted : ¬ (1000 * delsPerCall 100 ≤ 0 + 0) := by
  rw [dels_per_call]; decide

/-- 9. No tightening: the coupled restore clock equals `kPanAccessCall`. -/
def kPanStateRestoreCoupled : Nat := kPanAccessCall

theorem kPanStateRestoreCoupled_val :
    kPanStateRestoreCoupled = 159893274708 ∧ kPanStateRestoreCoupled = kPanAccessCall := by decide

/-- 10. `6×` still fails, `5×` passes. -/
theorem slopes :
    5 * kPanStateRestoreCoupled < yukon ∧ yukon < 6 * kPanStateRestoreCoupled := by decide

/-- 11. What a real tightening would need: if deletes were limited to `D + R` keys, the local
coefficient would return to `8` and `6×` would pass again (`kPanUnifiedAllTables` + truncation). -/
theorem hypothetical_fix :
    6 * (136116135658 + 3804281910) < yukon ∧ ¬ (6 * kPanStateRestoreCoupled < yukon) := by decide

end InitECandidate.Solver.GuestStateRestoreCoupledTightening
