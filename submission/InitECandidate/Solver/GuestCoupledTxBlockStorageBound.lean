import InitECandidate.Solver.GuestBs32BlockStorageEnvelope

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestCoupledTxBlockStorageBound`

Coupling of local (`ts+*`/`ev+*`, cluster size `dᵢ`) and block (`bs+32`, cluster size `D_{<i}`)
scans across the transactions of one 200M-gas block.

Coefficients (hand transcription of `guest.pp.pnk`, finds on the *storage-key* cluster only;
address-keyed tables `ts+8`, `ts+56`, outer `ts+32` hold one entry for the target address):
* warm `SSTORE` (l.7499): `ev+176`, `ts+24` (`get_storage`), inner `ts+32` (`stor_lookup`),
  inner `ts+32` ×2 (`jset` = `htab_get` + `htab_set`) ⇒ 5 local finds, `a = 10` ticks/slot;
  `get_storage_original` → `stor_lookup(bs+32)` always ⇒ 1 block find (`get_storage`'s `bs+32`
  lookup is skipped once the key is in `ts+32`) ⇒ `b = 2`.
* warm `SLOAD` (l.7482): `ev+176`, `ts+24`, inner `ts+32` ⇒ 3 local (`6`), `bs+32` ⇒ `2`.
  Dominated by `SSTORE`. Max: `a = 10`, `b = 2`.

Per tx `i`: `ticksᵢ ≤ wᵢ·(a·dᵢ + b·D_{<i})`. Coupling (`dᵢ + D_{<i} = D_{≤i} ≤ D`):
`Σ wᵢ(10dᵢ + 2D_{<i}) ≤ 8·Σ dᵢwᵢ + 2·D·W`, with `84·dᵢwᵢ ≤ mᵢ² ≤ 167,772·mᵢ` (EIP-7825).
Note: the block coefficient used in `GuestBs32BlockStorageEnvelope` (`2`) is confirmed;
the per-tx slope `14` there is replaced by the coupled local excess `8`.
-/

namespace InitECandidate.Solver.GuestCoupledTxBlockStorageBound

open InitECandidate.Solver.GuestBlockVsTxHtabBounds (blkRead)
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear kPanBs32Joint bs32_bs72_joint)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon maxGuestSourceClock)

/-- Local (`a`) and block (`b`) ticks per scanned slot for one warm op. -/
def a : Nat := 10
def b : Nat := 2
/-- EIP-7825 per-tx units. -/
def M : Nat := 167772

/-- Coupled ticks: tx list `(dᵢ, wᵢ)`, prefix block size `P`. -/
def coupled : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (d, w) :: t, P => w * (a * d + b * P) + coupled t (P + d)

def sumD (l : List (Nat × Nat)) : Nat := (l.map Prod.fst).sum
def sumW (l : List (Nat × Nat)) : Nat := (l.map Prod.snd).sum
def sumDW (l : List (Nat × Nat)) : Nat := (l.map (fun p => p.1 * p.2)).sum
def sumUnits (l : List (Nat × Nat)) : Nat := (l.map (fun p => 21 * p.1 + p.2)).sum

/-- 1. Constants. -/
theorem constants : a = 10 ∧ b = 2 ∧ a - b = 8 ∧ M = 167772 := by decide

/-- 2. **Coupling inequality** by induction on transactions:
`coupled l P ≤ 8·Σdw + 2·(P + Σd)·Σw`. -/
theorem coupling (l : List (Nat × Nat)) (P : Nat) :
    coupled l P ≤ 8 * sumDW l + 2 * ((P + sumD l) * sumW l) := by
  induction l generalizing P with
  | nil => simp [coupled]
  | cons x t ih =>
    obtain ⟨d, w⟩ := x
    have h := ih (P + d)
    simp only [coupled, sumDW, sumD, sumW, List.map_cons, List.sum_cons] at h ⊢
    unfold a b
    have e1 : w * (10 * d + 2 * P) = 8 * (d * w) + 2 * ((P + d) * w) := by ring
    have e2 : (P + d) * w ≤ (P + (d + (t.map Prod.fst).sum)) * w :=
      Nat.mul_le_mul_right _ (by omega)
    have e3 : (P + d + (t.map Prod.fst).sum) * (t.map Prod.snd).sum
        = (P + (d + (t.map Prod.fst).sum)) * (t.map Prod.snd).sum := by ring
    have e4 : (P + (d + (t.map Prod.fst).sum)) * (w + (t.map Prod.snd).sum)
        = (P + (d + (t.map Prod.fst).sum)) * w
          + (P + (d + (t.map Prod.fst).sum)) * (t.map Prod.snd).sum := by ring
    omega

/-- 3. Single-tx AM–GM: `84·d·w ≤ (21d + w)²`. -/
theorem amgm (d w : Nat) : 84 * (d * w) ≤ (21 * d + w) * (21 * d + w) := by
  have : (0 : Int) ≤ (21 * (d : Int) - w) ^ 2 := sq_nonneg _
  have h : (84 : Int) * (d * w) ≤ (21 * d + w) * (21 * d + w) := by nlinarith
  exact_mod_cast h

/-- 4. EIP-7825 local term: `84·Σ dᵢwᵢ ≤ M·Σ mᵢ` when every `mᵢ = 21dᵢ + wᵢ ≤ M`. -/
theorem local_sum (l : List (Nat × Nat)) (h : ∀ p ∈ l, 21 * p.1 + p.2 ≤ M) :
    84 * sumDW l ≤ M * sumUnits l := by
  induction l with
  | nil => simp [sumDW, sumUnits]
  | cons x t ih =>
    obtain ⟨d, w⟩ := x
    have hx := h (d, w) (by simp)
    have ht := ih (fun p hp => h p (by simp [hp]))
    simp only [sumDW, sumUnits, List.map_cons, List.sum_cons] at ht ⊢
    have h1 := amgm d w
    have h2 : (21 * d + w) * (21 * d + w) ≤ M * (21 * d + w) := Nat.mul_le_mul_right _ hx
    rw [Nat.mul_add M (21 * d + w)]; omega

/-- 5. Block budget ⇒ `Σ dᵢwᵢ ≤ 3,994,571,428`. -/
theorem local_le (l : List (Nat × Nat)) (h : ∀ p ∈ l, 21 * p.1 + p.2 ≤ M)
    (hS : sumUnits l ≤ S) : sumDW l ≤ 3994571428 := by
  have h1 := local_sum l h
  have h2 : M * sumUnits l ≤ M * S := Nat.mul_le_mul_left _ hS
  unfold M S at *; omega

/-- 6. `Σ(21dᵢ + wᵢ) = 21·Σd + Σw`. -/
theorem sumUnits_eq (l : List (Nat × Nat)) : sumUnits l = 21 * sumD l + sumW l := by
  induction l with
  | nil => simp [sumUnits, sumD, sumW]
  | cons x t ih =>
    simp only [sumUnits, sumD, sumW, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

/-- Coupled master envelope: linear + `8·⌊M·S/84⌋` + joint `bs+32`/`bs+72` term. -/
def kPanCoupled : Nat := linear + 8 * 3994571428 + 95238095238

/-- 7. **Master coupled bound** (all tx lists, `C` cold account reads sharing the budget). -/
theorem kPan_coupled_master (l : List (Nat × Nat)) (C : Nat)
    (h : ∀ p ∈ l, 21 * p.1 + p.2 ≤ M) (hS : sumUnits l + 21 * C ≤ S) :
    linear + coupled l 0 + blkRead C ≤ kPanCoupled := by
  have hc := coupling l 0
  have hl := local_le l h (by omega)
  have hu := sumUnits_eq l
  have hj := bs32_bs72_joint (sumD l) (sumW l) C (by omega)
  simp only [Nat.zero_add] at hc
  unfold kPanCoupled; unfold S at hj; omega

/-- 8. Value and strict improvement over `kPanBs32Joint`. -/
theorem kPanCoupled_val :
    kPanCoupled = 130854230896 ∧ kPanCoupled < kPanBs32Joint ∧
      kPanBs32Joint - kPanCoupled = 22227258243 := by decide

/-- 9. Slope `6×` now passes under the Yukon ceiling. -/
theorem slope6_ok : 6 * kPanCoupled < yukon := by decide

/-- 10. Exact integer slope threshold: `k · kPanCoupled < Yukon ↔ k ≤ 6` (so `9×`, `12×` fail). -/
theorem slope_threshold (k : Nat) : k * kPanCoupled < yukon ↔ k ≤ 6 := by
  unfold kPanCoupled linear yukon; omega

/-- 11. Tightness of the coupling on one tx: `coupled [(d,w)] 0 = 10·d·w`, equal to the bound. -/
theorem coupling_tight_single (d w : Nat) :
    coupled [(d, w)] 0 = 8 * sumDW [(d, w)] + 2 * ((0 + sumD [(d, w)]) * sumW [(d, w)]) := by
  simp [coupled, sumDW, sumD, sumW, a, b]; ring

/-- 12. Tightness of the local term: `(3994, 83898)` saturates one EIP-7825 tx
(`21·3994 + 83898 = 167,772`) with `84·d·w = 167,772²` up to rounding. -/
theorem local_tight :
    21 * 3994 + 83898 = M ∧ 84 * (3994 * 83898) ≤ M * M ∧ M * M - 84 * (3994 * 83898) < 84 * 83898 := by
  decide

/-- 13. Still above `maxGuestSourceClock`. -/
theorem above_max : maxGuestSourceClock < kPanCoupled := by decide

end InitECandidate.Solver.GuestCoupledTxBlockStorageBound
