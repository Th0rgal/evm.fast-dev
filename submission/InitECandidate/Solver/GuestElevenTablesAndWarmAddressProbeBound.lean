import InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound`

Hand transcription of `guest.pp.pnk` (wt-2). `is_warm_address` (l.6934) = `htab_has(ev+168, addr)`,
called by `access_gas_cost` for every address opcode (`BALANCE`, `EXTCODE*`, `CALL*`). `ev+168` is
per tx (sender + 18 precompiles + bought addresses, ≥ 30 units each), so its XOR-collision cluster
is `≤ a_t + 19`. Each warm address op costs ≥ 100 gas (1 unit) and probes it once
(`pFind = 2` ticks per entry, as in `HtabQuadraticCollisionMax`).

Not assumed absorbed in `12 A²` (that term covers `bs+8..bs+48`/`ts+*`); counted as new:
per tx `2(a+19)w`, with `30a + w ≤ M`, `Σ(30a + w) ≤ S`:
`120·a·w ≤ (30a + w)² ≤ M·(30a + w)` ⇒ `Σ a w ≤ M·S/120 = 2,796,200,000`,
`38·Σ w ≤ 76,000,000`. Term `≤ 5,668,400,000`.
`kPanElevenTables = kPanWarmSets + 5,668,400,000 = 167,431,989,338`; `5×` passes.
-/

namespace InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound

open InitECandidate.Solver.GuestWarmAccessSetAndRollbackBound (kPanWarmSets)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def M : Nat := 167772
def S : Nat := 2000000

/-- Probe ticks of one tx: `w` warm address ops on a cluster of `a + 19`. -/
def txProbe (p : Nat × Nat) : Nat := 2 * (p.1 + 19) * p.2

/-- 1. Single-tx AM-GM: `120 a w ≤ M (30 a + w)`. -/
theorem tx_amgm (a w : Nat) (h : 30 * a + w ≤ M) : 120 * (a * w) ≤ M * (30 * a + w) := by
  have h1 : 120 * (a * w) ≤ (30 * a + w) * (30 * a + w) := by
    nlinarith [sq_nonneg ((30 : Int) * a - w)]
  have h2 : (30 * a + w) * (30 * a + w) ≤ M * (30 * a + w) := Nat.mul_le_mul_right _ h
  omega

/-- 2. Tight: `a = 2,796`, `w = 83,892` saturates `M` and gives `aw = 234,562,032`. -/
theorem tx_amgm_val : 30 * 2796 + 83892 = M ∧ 2796 * 83892 = 234562032 := by decide

/-- 3. Block sum: `120 Σ a w ≤ M · Σ(30a + w)`. -/
theorem block_amgm (l : List (Nat × Nat)) (h : ∀ p ∈ l, 30 * p.1 + p.2 ≤ M) :
    120 * (l.map (fun p => p.1 * p.2)).sum ≤ M * (l.map (fun p => 30 * p.1 + p.2)).sum := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have hx := tx_amgm x.1 x.2 (h x (List.mem_cons_self ..))
    have ht := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    simp only [List.map_cons, List.sum_cons]
    nlinarith

/-- 4. `Σ a w ≤ 2,796,200,000` under the block budget. -/
theorem block_aw (l : List (Nat × Nat)) (h : ∀ p ∈ l, 30 * p.1 + p.2 ≤ M)
    (hS : (l.map (fun p => 30 * p.1 + p.2)).sum ≤ S) :
    (l.map (fun p => p.1 * p.2)).sum ≤ 2796200000 := by
  have := block_amgm l h
  have : M * (l.map (fun p => 30 * p.1 + p.2)).sum ≤ M * S := Nat.mul_le_mul_left _ hS
  unfold M S at *; omega

/-- 5. `M · S / 120` is exact. -/
theorem mS_div : M * S = 120 * 2796200000 := by decide

/-- 6. Expansion of the per-tx term. -/
theorem probe_expand (a w : Nat) : txProbe (a, w) = 2 * (a * w) + 38 * w := by
  unfold txProbe; ring

/-- 7. Block probe bound: `Σ txProbe ≤ 5,668,400,000`. -/
theorem probe_le (l : List (Nat × Nat)) (h : ∀ p ∈ l, 30 * p.1 + p.2 ≤ M)
    (hS : (l.map (fun p => 30 * p.1 + p.2)).sum ≤ S) :
    (l.map txProbe).sum ≤ 5668400000 := by
  have haw := block_aw l h hS
  have hw : (l.map Prod.snd).sum ≤ S := by
    refine le_trans ?_ hS
    clear h hS haw
    induction l with
    | nil => simp
    | cons x t ih => simp only [List.map_cons, List.sum_cons]; omega
  have e : (l.map txProbe).sum = 2 * (l.map (fun p => p.1 * p.2)).sum + 38 * (l.map Prod.snd).sum := by
    clear h hS haw hw
    induction l with
    | nil => simp
    | cons x t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [show x = (x.1, x.2) from rfl, probe_expand]; ring
  unfold S at hw; omega

/-- 8. Components of the term. -/
theorem probe_parts : 2 * 2796200000 + 38 * 2000000 = 5668400000 := by decide

/-- Eleven-table envelope. -/
def kPanElevenTables : Nat := kPanWarmSets + 5668400000

/-- 9. Value. -/
theorem kPan_val : kPanElevenTables = 167431989338 := by decide

/-- 10. `5×` passes with exact margin; `6×` fails. -/
theorem slopes :
    5 * kPanElevenTables < yukon ∧ yukon - 5 * kPanElevenTables = 63559978784 ∧
      yukon < 6 * kPanElevenTables := by decide

end InitECandidate.Solver.GuestElevenTablesAndWarmAddressProbeBound
