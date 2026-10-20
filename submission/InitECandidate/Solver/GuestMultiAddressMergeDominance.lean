import InitECandidate.Solver.GuestMergeTxUnionEnvelope

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestMultiAddressMergeDominance`

Multi-address generalisation of `GuestMergeTxUnionEnvelope` (hand transcription, `guest.pp.pnk`).

Block-level keyed tables: storage inner tables of `bs+32` (`D_a` keys per address `a`), the outer
table of `bs+32`, and the address tables `bs+8/16/24/40/48/72`. A warm probe (1 unit: `SLOAD`,
`SSTORE`, `BALANCE`, …) scans, in each table it touches, the cluster of its key at 2 ticks/slot
(`htab_find_slot` iteration + `memeq`). Each block-table entry is created by an op costing
≥ 20 units (storage: 19 warm + 1 or 21 cold; address: cold access ≥ 26).

Model: let `X = Σ_tables entries` (with multiplicity across tables) and `W` the warm probes.
Per probe, block scans `≤ 2·X`; merge inserts `≤ 2·X` per entry. Budget `20X + (W + X) ≤ S`.
* Per-address split: `Σ_a D_a(W_a + D_a) ≤ D(W + D)` (inner tables only see their own address).
* Joint: `2X(W + X) ≤ S²/40 = 100,000,000,000` — exactly the single-address vertex of
  `GuestMergeTxUnionEnvelope`; addresses cost ≥ 26 > 20, so they never improve on storage keys.
* Address merge scans (6 tables, `cap ≤ 2·entries`) stay in `mergeLin`.
Hypotheses (not derived from code): every block-table entry costs ≥ 20 units of its own; one probe
scans each block entry at most once per table.
-/

namespace InitECandidate.Solver.GuestMultiAddressMergeDominance

open InitECandidate.Solver.GuestMergeTxUnionEnvelope
  (kPanMerge mergeLin blockMerge locCoup merge_block_le)
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- 1. Per-address split of the inner `bs+32` term: `Σ D_a(W_a + D_a) ≤ D·(W + D)`. -/
theorem per_address_split (l : List (Nat × Nat)) :
    (l.map (fun p => p.1 * (p.2 + p.1))).sum ≤
      (l.map Prod.fst).sum * ((l.map Prod.snd).sum + (l.map Prod.fst).sum) := by
  induction l with
  | nil => simp
  | cons x t ih =>
    obtain ⟨d, w⟩ := x
    simp only [List.map_cons, List.sum_cons]
    have e : (d + (t.map Prod.fst).sum) * (w + (t.map Prod.snd).sum + (d + (t.map Prod.fst).sum))
        = d * (w + d) + d * ((t.map Prod.snd).sum + (t.map Prod.fst).sum) + d * (t.map Prod.fst).sum
          + (t.map Prod.fst).sum * ((t.map Prod.snd).sum + (t.map Prod.fst).sum)
          + (t.map Prod.fst).sum * w := by ring
    omega

/-- 2. Tightness of (1): equality with a single address. -/
theorem per_address_tight (d w : Nat) :
    ([(d, w)].map (fun p => p.1 * (p.2 + p.1))).sum =
      ([(d, w)].map Prod.fst).sum * (([(d, w)].map Prod.snd).sum + ([(d, w)].map Prod.fst).sum) := by
  simp

/-- 3. Address-only block term: `26A + W ≤ t ⇒ 104·A·W ≤ t²`. -/
theorem addr_square (A W t : Nat) (h : 26 * A + W ≤ t) : 104 * (A * W) ≤ t * t := by
  have h' : (26 * (A : Int) + W) ≤ t := by exact_mod_cast h
  have hA : (0 : Int) ≤ A := by positivity
  have hm : (A : Int) * W ≤ A * (t - 26 * A) := Int.mul_le_mul_of_nonneg_left (by linarith) hA
  have hsq : (0 : Int) ≤ ((t : Int) - 52 * A) ^ 2 := sq_nonneg _
  have : (104 : Int) * (A * W) ≤ t * t := by nlinarith
  exact_mod_cast this

/-- 4. Address keys are strictly worse per unit than storage keys: `S²/52 < S²/42`. -/
theorem addr_dominated : S * S / 52 < S * S / 42 := by decide

/-- 5. **Joint multi-table block term**: storage keys `D` (≥ 20 units) and address entries `A`
(≥ 26 units) sharing the probes `W`: `20D + 26A + (W + D + A) ≤ S ⇒ 80·(D+A)(W+D+A) ≤ S²`. -/
theorem joint_multi (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    80 * ((D + A) * (W + (D + A))) ≤ S * S := by
  have h2 : 20 * (D + A) + (W + (D + A)) ≤ S := by omega
  exact InitECandidate.Solver.GuestMergeTxUnionEnvelope.merge_block_square (D + A) W h2

/-- 6. Integer form: `2·(D+A)·(W+D+A) ≤ 100,000,000,000 = blockMerge`. -/
theorem joint_multi_le (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    2 * ((D + A) * (W + (D + A))) ≤ blockMerge := by
  have h2 : 20 * (D + A) + (W + (D + A)) ≤ S := by omega
  exact merge_block_le (D + A) W h2

/-- 7. Vertex is single-address (`A = 0`, `D = 50,000`, `W = 950,000`); any `A ≥ 1` costs budget. -/
theorem vertex_single_address :
    20 * 50000 + 26 * 0 + (950000 + 50000 + 0) = S ∧
      2 * ((50000 + 0) * (950000 + (50000 + 0))) = blockMerge := by decide

/-- 8. Address merge linear scans: `6` tables × (`2A` slots + `A` inserts) with `26A ≤ S` stay
inside `mergeLin` together with the storage scan `3D` (`21D ≤ S`). -/
theorem addr_merge_linear (D A : Nat) (h : 21 * D + 26 * A ≤ S) : 3 * D + 18 * A ≤ mergeLin := by
  unfold S at h; unfold mergeLin; omega

/-- Multi-address merge-aware source clock (same envelope). -/
def kPanMultiAddrMerge : Nat := linear + locCoup + blockMerge + mergeLin

/-- 9. Equal to `kPanMerge`: lifting the single-address hypothesis costs nothing. -/
theorem kPanMultiAddrMerge_eq : kPanMultiAddrMerge = kPanMerge ∧ kPanMultiAddrMerge = 136116135658 := by
  decide

/-- 10. **Master bound** over all `(D, A, W)` and per-tx local / linear terms. -/
theorem master (D A W Tloc Tlin : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + 2 * ((D + A) * (W + (D + A))) + Tlin ≤ kPanMultiAddrMerge := by
  have := joint_multi_le D A W h
  unfold kPanMultiAddrMerge; omega

/-- 11. Target slopes `3×, 4×, 5×, 6×` under Yukon. -/
theorem slopes_ok :
    3 * kPanMultiAddrMerge < yukon ∧ 4 * kPanMultiAddrMerge < yukon ∧
      5 * kPanMultiAddrMerge < yukon ∧ 6 * kPanMultiAddrMerge < yukon := by decide

/-- 12. Exact threshold `k ≤ 6` and margin `84,023,111,526` at `6×`. -/
theorem threshold_and_margin (k : Nat) :
    (k * kPanMultiAddrMerge < yukon ↔ k ≤ 6) ∧ yukon - 6 * kPanMultiAddrMerge = 84023111526 := by
  refine ⟨?_, by decide⟩
  unfold kPanMultiAddrMerge linear locCoup blockMerge mergeLin yukon; omega

end InitECandidate.Solver.GuestMultiAddressMergeDominance
