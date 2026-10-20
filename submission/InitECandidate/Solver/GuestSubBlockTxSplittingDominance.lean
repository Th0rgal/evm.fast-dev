import InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestSubBlockTxSplittingDominance`

Splitting a block into `T` transactions never beats one concentrated transaction
(hand transcription of `guest.pp.pnk`, wt-2).

Code facts:
* There is no `tx_clear`; the per-tx reset is `state_fresh_tx` (l.5419): 8 × `htab_new` with caps
  64/64/64/16/16/16/16/16 (each: 6 `alloc` + `memzero(cap)`) plus `alloc(72)` — a constant
  `≤ txResetTicks = 200` ticks per tx.
* Minimum intrinsic gas (`calculate_intrinsic_cost`, l.5298): `base_regular_gas = 12000 +
  recipient` (≥ 12,000 gas = 120 units, not 21,000 in this Guest).
* Access-list storage key (l.5327): `(2100 − 100) + 128·16 = 4,048` gas ≥ 40 units, so the
  `R`-transition (warm key + 1) costs ≥ 41 units here, above the 20 used upstream (safe).

Splitting: transaction-local tables see only `(D_t, A_t, C_t)`, block tables see the prefix
`D_{≤t} ≤ D`. Generic algebra: `Σ aₜbₜ ≤ (Σa)(Σb)`, `Σ aₜ² ≤ (Σa)²`, `Σ D_{≤t}·wₜ ≤ D·W`.
-/

namespace InitECandidate.Solver.GuestSubBlockTxSplittingDominance

open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope (kPanUnifiedAllTables)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Per-tx local objective. -/
def localCost (x : Nat × Nat × Nat × Nat × Nat) : Nat :=
  let (D, R, A, C, W) := x
  D * (2 * W + 4 * R) + 12 * (A * A) + C * (W + C)

def sD (l : List (Nat × Nat × Nat × Nat × Nat)) : Nat := (l.map (·.1)).sum
def sR (l : List (Nat × Nat × Nat × Nat × Nat)) : Nat := (l.map (·.2.1)).sum
def sA (l : List (Nat × Nat × Nat × Nat × Nat)) : Nat := (l.map (·.2.2.1)).sum
def sC (l : List (Nat × Nat × Nat × Nat × Nat)) : Nat := (l.map (·.2.2.2.1)).sum
def sW (l : List (Nat × Nat × Nat × Nat × Nat)) : Nat := (l.map (·.2.2.2.2)).sum

/-- 1. **Splitting sub-additivity** for the local objective, by induction on the tx list. -/
theorem split_local_le (l : List (Nat × Nat × Nat × Nat × Nat)) :
    (l.map localCost).sum ≤ localCost (sD l, sR l, sA l, sC l, sW l) := by
  induction l with
  | nil => simp [localCost, sD, sR, sA, sC, sW]
  | cons x t ih =>
    obtain ⟨D, R, A, C, W⟩ := x
    simp only [List.map_cons, List.sum_cons, sD, sR, sA, sC, sW, localCost] at ih ⊢
    generalize (t.map (·.1)).sum = d at ih ⊢
    generalize (t.map (·.2.1)).sum = r at ih ⊢
    generalize (t.map (·.2.2.1)).sum = a at ih ⊢
    generalize (t.map (·.2.2.2.1)).sum = c at ih ⊢
    generalize (t.map (·.2.2.2.2)).sum = w at ih ⊢
    generalize (t.map localCost).sum = s at ih ⊢
    nlinarith [Nat.zero_le (D * w), Nat.zero_le (d * W), Nat.zero_le (D * r), Nat.zero_le (d * R),
      Nat.zero_le (A * a), Nat.zero_le (C * w), Nat.zero_le (c * W), Nat.zero_le (C * c)]

/-- 2. Strictness for `T = 2`: two unit txs cost `40` < `80` for the merged tx. -/
theorem split_strict :
    localCost (1, 1, 1, 1, 1) + localCost (1, 1, 1, 1, 1) = 40 ∧ localCost (2, 2, 2, 2, 2) = 80 := by
  decide

/-- Block-prefix probe cost: tx `t` with `wₜ` probes sees the prefix `P + dₜ`. -/
def prefixCost : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (d, w) :: t, P => (P + d) * w + prefixCost t (P + d)

/-- 3. **Prefix probes ≤ concentrated**: `prefixCost l P ≤ (P + Σd)·Σw`. -/
theorem prefix_le (l : List (Nat × Nat)) (P : Nat) :
    prefixCost l P ≤ (P + (l.map Prod.fst).sum) * (l.map Prod.snd).sum := by
  induction l generalizing P with
  | nil => simp [prefixCost]
  | cons x t ih =>
    obtain ⟨d, w⟩ := x
    have h := ih (P + d)
    simp only [prefixCost, List.map_cons, List.sum_cons]
    generalize (t.map Prod.fst).sum = sd at h ⊢
    generalize (t.map Prod.snd).sum = sw at h ⊢
    generalize prefixCost t (P + d) = pc at h ⊢
    nlinarith [Nat.zero_le (sd * w)]

/-- 4. Equality case: one tx, `prefixCost [(D, W)] 0 = D·W`. -/
theorem prefix_tight (D W : Nat) : prefixCost [(D, W)] 0 = D * W := by
  simp [prefixCost]

/-- 5. Prefix strictness: two txs `(1,1),(1,1)` give `3 < 4`. -/
theorem prefix_strict : prefixCost [(1, 1), (1, 1)] 0 = 3 ∧ 3 < (0 + 2) * 2 := by decide

/-- Constant per-tx reset (`state_fresh_tx`) and its minimal gas in 100-gas units. -/
def txResetTicks : Nat := 200
def txMinUnits : Nat := 120

/-- 6. `state_fresh_tx` cost: 8 tables × (6 allocs + call + `memzero` ≤ 1 + 64/32 + 3) + 2 ≤ 200. -/
theorem reset_bound : 8 * (6 + 1 + (1 + 64 / 32 + 3)) + 2 ≤ txResetTicks := by decide

/-- 7. Reset absorbed by the linear envelope: 200 ticks ≤ 18 ticks/gas × 12,000 gas, so any
`T` with `120·T ≤ S` adds `≤ 200·T ≤ 18·12000·T`, already inside `18·gas`. -/
theorem reset_absorbed (T : Nat) (h : txMinUnits * T ≤ 2000000) :
    txResetTicks * T ≤ 18 * (12000 * T) ∧ T ≤ 16666 := by
  unfold txMinUnits at h; unfold txResetTicks; omega

/-- 8. Max transactions per block at minimal intrinsic gas: `16,666`, total reset `3,333,200`. -/
theorem max_tx_reset : txMinUnits * 16666 ≤ 2000000 ∧ 2000000 < txMinUnits * 16667 ∧
    txResetTicks * 16666 = 3333200 := by decide

/-- 9. Access-list key cost from `calculate_intrinsic_cost`: `4,048` gas ≥ 20 units used upstream. -/
theorem access_list_key_cost : (2100 - 100) + 128 * 16 = 4048 ∧ 2000 ≤ 4048 := by decide

/-- 10. Worst case over all splittings stays `kPanUnifiedAllTables`, and `6×` passes Yukon. -/
theorem split_master (l : List (Nat × Nat × Nat × Nat × Nat)) (bound : Nat)
    (hb : localCost (sD l, sR l, sA l, sC l, sW l) ≤ bound) :
    (l.map localCost).sum ≤ bound ∧ 6 * kPanUnifiedAllTables < yukon ∧
      kPanUnifiedAllTables = 136116135658 :=
  ⟨le_trans (split_local_le l) hb, by decide, by decide⟩

end InitECandidate.Solver.GuestSubBlockTxSplittingDominance
