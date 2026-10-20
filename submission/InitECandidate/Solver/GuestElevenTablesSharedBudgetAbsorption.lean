import InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption`

Shared block budget `B + u₂ + u₃ + u₄ ≤ S` between
(1) storage/revert regime on `B` units: `40·blk ≤ B²`, `84·loc ≤ M·B`, cost `blk + 13·loc`;
(2) `ev+176` truncation: `21·t₂ ≤ 5·7,989·u₂` (one 21-unit cold key per deleted entry);
(3) `ev+168` truncation: `30·t₃ ≤ 5·5,611·u₃`;
(4) `ev+168` probes: `60·t₄ ≤ (M + 2,280)·u₄` (from `120 a w ≤ M(30a + w)` and `38 w`).
Marginal slopes of (2)–(4) are `≤ 2,835` ticks/unit; the storage regime loses at least
`(S² − B²)/40 ≥ 50,000·(S − B)` ticks when `S − B` units leave it. Hence (2)–(4) are absorbed:
`blk + 13 loc + t₂ + t₃ + t₄ ≤ 151,929,428,571`.
`kPanElevenTablesShared = 156,088,992,805`. Witness (12 txs, `GuestCoupledRevertAndTxCapTightening`)
`155,688,931,265`: the worst case lies in this interval (gap `400,061,540`).
Margin at `5×`: `120,274,961,449` (not `120,275,036,010`). `6×` fails.
-/

namespace InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption

open InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound (kPanElevenTables)
open InitECandidate.Solver.GuestCoupledRevertAndTxCapTightening (coupledCost witness feasible
  witness_feasible witness_cost)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def M : Nat := 167772
def S : Nat := 2000000

/-- 1. Per-unit slopes of the three side regimes are below `2,834`. -/
theorem side_slopes : 5 * 7989 ≤ 21 * 1903 ∧ 5 * 5611 ≤ 30 * 936 ∧ M + 2280 ≤ 60 * 2835 := by decide

/-- 2. Storage regime loses ≥ `50,000` per unit moved out (`(S² − B²)/40 ≥ S(S − B)/40`). -/
theorem storage_loss (B : Nat) (hB : B ≤ S) : S * (S - B) ≤ S * S - B * B := by
  unfold S at *
  have : B * B ≤ 2000000 * B := Nat.mul_le_mul_right _ hB
  have e : 2000000 * (2000000 - B) = 2000000 * 2000000 - 2000000 * B := Nat.mul_sub _ _ _
  omega

/-- 3. **Shared-budget absorption** (all regimes on one budget). The bound is
`⌊(21 S² + 130 M S)/840⌋ = 151,929,428,571` (7 ticks above `10¹¹ + 13·3,994,571,428`, from the floor
in `locCoup`). -/
theorem shared_absorption (B u2 u3 u4 blk loc t2 t3 t4 : Nat)
    (hS : B + u2 + u3 + u4 ≤ S) (hblk : 40 * blk ≤ B * B) (hloc : 84 * loc ≤ M * B)
    (h2 : 21 * t2 ≤ 5 * 7989 * u2) (h3 : 30 * t3 ≤ 5 * 5611 * u3) (h4 : 60 * t4 ≤ (M + 2280) * u4) :
    blk + 13 * loc + t2 + t3 + t4 ≤ 151929428571 := by
  unfold S M at *
  have hB : B ≤ 2000000 := by omega
  have hsq : B * B ≤ 2000000 * B := Nat.mul_le_mul_right _ hB
  -- 840·LHS ≤ 21 B² + 130 M B + 2,380,560 (u₂+u₃+u₄) ≤ (21 S + 130 M)(B + u) ≤ (21 S + 130 M) S
  have hb2 : 21 * (B * B) ≤ 42000000 * B := by omega
  have hall : 63810360 * (B + u2 + u3 + u4) ≤ 63810360 * 2000000 := Nat.mul_le_mul_left _ hS
  have e1 : 63810360 * (B + u2 + u3 + u4) = 63810360 * B + 63810360 * u2 + 63810360 * u3 + 63810360 * u4 := by ring
  have m2 : 5 * 7989 * u2 = 39945 * u2 := by ring
  have m4 : (167772 + 2280) * u4 = 170052 * u4 := by ring
  have m3 : 5 * 5611 * u3 = 28055 * u3 := by ring
  have mb : 167772 * B = 167772 * B := rfl
  omega

/-- 4. Exact at the storage corner: `B = S`, `blk = 10¹¹`, `loc = 3,994,571,428`, no side regime. -/
theorem shared_tight :
    40 * 100000000000 ≤ S * S ∧ 84 * 3994571428 ≤ M * S ∧
      (21 * S * S + 130 * M * S) / 840 = 151929428571 := by decide

/-- Shared envelope: linear + merge scan + absorbed quadratic terms. -/
def kPanElevenTablesShared : Nat := 3659564234 + 500000000 + 151929428571

/-- 5. Value and gain over `kPanElevenTables`. -/
theorem kPan_val : kPanElevenTablesShared = 156088992805 ∧
    kPanElevenTables - kPanElevenTablesShared = 11342996533 := by decide

/-- 6. Feasible lower witness (12 txs). -/
theorem lower_witness : feasible witness ∧ coupledCost witness = 155688931265 :=
  ⟨witness_feasible, witness_cost⟩

/-- 7. **Bracket** of the worst case and its width. -/
theorem bracket : coupledCost witness ≤ kPanElevenTablesShared ∧
    kPanElevenTablesShared - coupledCost witness = 400061540 := by
  rw [witness_cost]; decide

/-- 8. Relative width `< 0.26 %`. -/
theorem bracket_rel : 400061540 * 10000 < 26 * 156088992805 := by decide

/-- 9. `5×` passes with exact margin. -/
theorem five_margin :
    5 * kPanElevenTablesShared < yukon ∧ yukon - 5 * kPanElevenTablesShared = 120274961449 := by
  decide

/-- 10. `6×` fails even at the lower witness: no envelope in this model restores it. -/
theorem six_fails : yukon < 6 * kPanElevenTablesShared ∧ yukon < 6 * coupledCost witness := by
  rw [witness_cost]; decide

end InitECandidate.Solver.GuestElevenTablesSharedBudgetAbsorption
