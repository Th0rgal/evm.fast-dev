import InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption`

Hand inventory of `guest.pp.pnk` (wt-2; `Spec/Guest.lean` and `submission/InitECandidate/Guest.lean`
do not exist). 32 `htab_new` + 2 `htab_new_scratch` sites. Tables beyond the 11 counted so far:
* `ts+56` (created accounts, `mark_account_created` l.5829; insert needs `CREATE` ≥ 32,000 gas);
* **`ts+64` (transient storage, `get_transient_storage` l.5686 / `set_transient_storage` l.5832)**:
  `op_tstore`/`op_tload` charge **100 gas**, key `addr‖key` (52 bytes, `sk_make`), no cold surcharge,
  unsalted XOR-fold `htab_hash`, linear probing in `htab_find_slot` (l.~1690). Reset per tx;
* `ev+136` (per-frame scratch, merged by `htab_union_into` l.8636);
* `bal_accounts`, `bal_idx_accts`, `bal_idx_stor` (block access list, `bal_init` l.5982) — not audited;
* `ws+32`, `nodedb` (l.3696), `new_roots` (l.14662), `written`/`set_for` (l.8074, EIP-7702) — not audited.

`general_side_regime_absorption` (below) absorbs any regime of slope ≤ 50,000 ticks/unit.
**`ts+64` violates that hypothesis**: the `i`-th colliding transient key costs ≥ `2(i − 1)` ticks
(one find, 1 loop tick + 1 `memeq` call per probed entry) for ≤ 2 units, so its marginal slope reaches
`≈ 83,826` ticks/unit at the per-tx cap. Absorption depends on the tick model: with one find and 2 units/key the
*summed* slope stays ≤ 50,000 (absorbed); with the real `jset` path (two finds) at ~1 unit/key one tx
alone gives `56.2 G` at slope `> 335,000` (not absorbed; 11 txs ≈ 618 G). No upper bound on `ts+64`
is proved here.
-/

namespace InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def S : Nat := 2000000

/-- 1. **General side-regime absorption** (scalar form). -/
theorem side_absorption_scalar (B U T blk : Nat) (hS : B + U ≤ S) (hblk : 40 * blk ≤ B * B)
    (hT : T ≤ 50000 * U) : blk + T ≤ 100000000000 := by
  unfold S at hS
  have hB : B * B ≤ 2000000 * B := Nat.mul_le_mul_right _ (by omega)
  have hU : 2000000 * U ≤ 2000000 * (2000000 - B) := Nat.mul_le_mul_left _ (by omega)
  have e : 2000000 * (2000000 - B) = 4000000000000 - 2000000 * B := by
    rw [Nat.mul_sub]
  omega

/-- 2. **`general_side_regime_absorption`**: any list of side regimes `(tᵢ, uᵢ)` with
`Σ tᵢ ≤ 50,000 · Σ uᵢ` sharing `B + Σ uᵢ ≤ S` with `40·blk ≤ B²`. -/
theorem general_side_regime_absorption (l : List (Nat × Nat)) (B blk : Nat)
    (hS : B + (l.map Prod.snd).sum ≤ S) (hblk : 40 * blk ≤ B * B)
    (hslope : (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum) :
    blk + (l.map Prod.fst).sum ≤ 100000000000 :=
  side_absorption_scalar B _ _ blk hS hblk hslope

/-- 3. Per-regime slopes imply the summed slope hypothesis. -/
theorem slope_sum (l : List (Nat × Nat)) (h : ∀ p ∈ l, p.1 ≤ 50000 * p.2) :
    (l.map Prod.fst).sum ≤ 50000 * (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    simp only [List.map_cons, List.sum_cons]; omega

/-- 4. Tight: `blk = 10¹¹` at `B = S`, no side regime. -/
theorem absorption_tight : 40 * 100000000000 = S * S ∧ 100000000000 + 0 = 100000000000 := by decide

/-- 5. The `50,000` threshold is sharp: one more tick per unit breaks the bound. -/
theorem threshold_sharp :
    ¬ (∀ B U T blk : Nat, B + U ≤ S → 40 * blk ≤ B * B → T ≤ 50001 * U → blk + T ≤ 100000000000) := by
  intro h
  have := h 0 2000000 (50001 * 2000000) 0 (by decide) (by decide) le_rfl
  omega

/-- 6. Already absorbed regimes: `ev+176`/`ev+168` truncation and `ev+168` probes (slopes ≤ 2,835),
`ts+56` creates (≥ 320 units each, ≤ 2·2·10⁶/320 per insert). -/
theorem known_slopes : 5 * 7989 ≤ 21 * 50000 ∧ 5 * 5611 ≤ 30 * 50000 ∧
    167772 + 2280 ≤ 60 * 50000 ∧ 2 * 6250 ≤ 320 * 50000 := by decide

/-- Lower-bound ticks of `k` colliding transient keys in one tx (one find, 2 ticks per entry). -/
def tstoreTicks (k : Nat) : Nat := k * (k - 1)

/-- 7. `ts+64` breaks the slope hypothesis: the marginal key at cluster `83,826` costs
`2 · 83,825` ticks for 2 units, i.e. `83,825 > 50,000` ticks/unit. -/
theorem tstore_slope_exceeds : tstoreTicks 83826 - tstoreTicks 83825 = 2 * 83825 ∧ 50000 < 83825 := by
  decide

/-- 8. Per-tx feasibility at 2 units/`TSTORE` (12,000 gas intrinsic = 120 units). -/
theorem tstore_tx_budget : 120 + 2 * 83826 ≤ 167772 ∧ 11 * 167772 + 120 + 2 * 77194 ≤ S := by decide

/-- 9. Conservative `ts+64` lower witness for the block. -/
theorem tstore_witness : 11 * tstoreTicks 83826 + tstoreTicks 77194 = 83252695392 := by decide

/-- 10. Sensitivity. (a) Minimal model (one find, 2 units/key): the block witness averages
`83,252,695,392 ≤ 50,000 · 1,999,960` — summed slope hypothesis holds despite marginal excess.
(b) `jset` model (`set_transient_storage` → `jset` = `htab_get` + `htab_set`: two finds, 4 ticks/entry)
at ~1 unit/key (`op_tstore` charges 100 gas; ~6 gas of PUSHes): one tx of 167,652 keys alone gives
`2·k(k−1) = 56,214,050,904` ticks for 167,772 units, slope `> 335,000`: not absorbed. -/
theorem tstore_sensitivity :
    83252695392 ≤ 50000 * (11 * 2 * 83826 + 2 * 77194) ∧
      2 * tstoreTicks 167652 = 56214050904 ∧ 50000 * 167772 < 2 * tstoreTicks 167652 := by decide

end InitECandidate.Solver.GuestExhaustiveHtabInventoryAndSlopeAbsorption
