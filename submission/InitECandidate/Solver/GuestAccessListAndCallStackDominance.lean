import InitECandidate.Solver.GuestSubBlockTxSplittingDominance

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestAccessListAndCallStackDominance`

Hand transcription of `guest.pp.pnk` (wt-2).

## Access list (tx setup, l.~15260 and `calculate_intrinsic_cost` l.5298)
`aa = htab_new(20, 64)`: sender, 18 precompiles, every access-list address; `ak = htab_new(52, 16)`:
every access-list storage key. These become the frame warm sets `ev+168` / `ev+176` (tx-local).
Intrinsic gas: address `(3000 − 100) + 80·16 = 4,180`, key `(2100 − 100) + 128·16 = 4,048`.
An access-list key enters exactly the `ev+176` cluster a cold access would fill (21 units), at
≥ 40 units: dominated. (The request's `2,400 + 20·16 = 2,720` for an address is not this Guest.)

## Call stack and revert
* Depth guard `msg+128 + 1 > 1024` (l.8732, l.8818).
* Journal: `jset`/`jdel` push entries; `state_restore(snap)` (l.5481) pops each entry and replays
  `htab_set` or `htab_del` on its table. `rollback_child_access` (l.8639) `htab_truncate`s the
  child's `ev+168/176` back to the parent size (one `htab_del` per added warm entry).
* `htab_del` (l.1682): one `htab_find_slot` + backward-shift loop over the cluster run
  (per iteration: 1 tick + `htab_hash` call + `memcpy` call ≤ 3 ticks).

New quadratic cost: a reverted `SSTORE` journal entry costs `≤ 2d + 3d = 5d` ticks on its
`d`-sized inner `ts+32` cluster. Every entry comes from one warm `SSTORE` (≥ 1 unit) and is undone at
most once, so the local per-probe excess rises from `8` to `13`: `+5 · 3,994,571,428`.
Warm-set truncation: each deleted `ev+176` entry was a cold access (≥ 21 units, `≤ 7,989` per
EIP-7825 tx): `≤ 5 · 7,989 · 95,238 = 3,804,281,910`.
Result: `kPanAccessCall = 159,893,274,708`; slopes `3×, 4×, 5×` pass Yukon, **`6×` fails**.
Per-call frame overhead is linear and assumed inside the `18` ticks/gas envelope (not recounted).
-/

namespace InitECandidate.Solver.GuestAccessListAndCallStackDominance

open InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope (kPanUnifiedAllTables)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Access-list intrinsic costs in gas. -/
def alAddrGas : Nat := (3000 - 100) + 80 * 16
def alKeyGas : Nat := (2100 - 100) + 128 * 16

/-- 1. Exact access-list costs from `calculate_intrinsic_cost`. -/
theorem al_costs : alAddrGas = 4180 ∧ alKeyGas = 4048 := by decide

/-- 2. Access-list entries are strictly more expensive per entry than the modelled `A` (26) and
`D`/`C` (21) units. -/
theorem al_dominated : 26 * 100 < alAddrGas ∧ 21 * 100 < alKeyGas ∧ 20 * 100 < alKeyGas := by decide

/-- 3. Budget domination: any `(Kal, Aal)` paid at ≥ 40 / 41 units fits the cheaper modelled budget,
so it can only shrink the feasible cold/warm counts. -/
theorem al_budget (Kal Aal D A C R W : Nat)
    (h : 40 * Kal + 41 * Aal + 21 * D + 20 * R + 26 * A + 21 * C + W ≤ 2000000) :
    21 * (D + Kal) + 20 * R + 26 * (A + Aal) + 21 * C + W ≤ 2000000 := by omega

/-- Ticks of undoing one journal entry on a cluster of size `d` (find + backward shift). -/
def undoTicks (d : Nat) : Nat := 2 * d + 3 * d

/-- 4. `undoTicks d = 5d`. -/
theorem undo_eq (d : Nat) : undoTicks d = 5 * d := by unfold undoTicks; omega

/-- Revert cost of a tx list `(dₜ, wₜ)`: each of the `wₜ` journal entries undone on `dₜ`. -/
def revertCost (l : List (Nat × Nat)) : Nat := (l.map (fun p => p.2 * undoTicks p.1)).sum

/-- 5. Revert cost is exactly `5 · Σ dₜwₜ`. -/
theorem revert_eq (l : List (Nat × Nat)) :
    revertCost l = 5 * (l.map (fun p => p.1 * p.2)).sum := by
  induction l with
  | nil => simp [revertCost]
  | cons x t ih =>
    simp only [revertCost, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, undo_eq]; ring

/-- 6. Under EIP-7825 + block budget (`Σ dw ≤ 3,994,571,428`), revert ticks `≤ 19,972,857,140`. -/
theorem revert_le (l : List (Nat × Nat)) (h : (l.map (fun p => p.1 * p.2)).sum ≤ 3994571428) :
    revertCost l ≤ 19972857140 := by rw [revert_eq]; omega

/-- 7. Warm-set truncation: `c ≤ 7,989` cold keys per tx, `≤ 95,238` per block:
`5 · 7,989 · 95,238 = 3,804,281,910`, and `7,989` is the EIP-7825 max. -/
theorem truncate_le (c n : Nat) (hc : c ≤ 7989) (hn : n ≤ 95238) :
    5 * c * n ≤ 3804281910 ∧ 21 * 7989 ≤ 167772 ∧ 167772 < 21 * 7990 := by
  refine ⟨?_, by decide, by decide⟩
  have : c * n ≤ 7989 * 95238 := Nat.mul_le_mul hc hn
  calc 5 * c * n = 5 * (c * n) := by ring
    _ ≤ 5 * (7989 * 95238) := by omega
    _ = 3804281910 := by decide

/-- 8. Depth guard: a call at depth `d` proceeds only if `d + 1 ≤ 1024`. -/
theorem depth_guard (d : Nat) (h : ¬ (d + 1 > 1024)) : d ≤ 1023 := by omega

/-- Envelope including access list, calls and reverts. -/
def kPanAccessCall : Nat := kPanUnifiedAllTables + 19972857140 + 3804281910

/-- 9. Value. -/
theorem kPanAccessCall_val : kPanAccessCall = 159893274708 := by decide

/-- 10. Slopes `3×, 4×, 5×` pass Yukon; `6×` now fails. -/
theorem slopes :
    3 * kPanAccessCall < yukon ∧ 4 * kPanAccessCall < yukon ∧ 5 * kPanAccessCall < yukon ∧
      yukon < 6 * kPanAccessCall := by decide

/-- 11. Exact threshold `k ≤ 5`, margin at `5×`. -/
theorem threshold (k : Nat) :
    (k * kPanAccessCall < yukon ↔ k ≤ 5) ∧ yukon - 5 * kPanAccessCall = 101253551934 := by
  refine ⟨?_, by decide⟩
  unfold kPanAccessCall kPanUnifiedAllTables
    InitECandidate.Solver.GuestBs32BlockStorageEnvelope.linear
    InitECandidate.Solver.GuestMergeTxUnionEnvelope.locCoup
    InitECandidate.Solver.GuestMergeTxUnionEnvelope.mergeLin yukon
  omega

end InitECandidate.Solver.GuestAccessListAndCallStackDominance
