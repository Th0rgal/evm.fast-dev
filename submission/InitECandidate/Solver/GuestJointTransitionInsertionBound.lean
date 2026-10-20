import InitECandidate.Solver.GuestSstoreCleanToDirtyTransition

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestJointTransitionInsertionBound`

The local `ts+32` insertion cost of clean→dirty transitions is linear in `R = Σ rᵢ`
(`5·r(r−1) ≤ 41,935·r` under EIP-7825 `20r ≤ 167,772`), and the joint block objective
`F = D(2W + 4R) + 41,935·R` under `21D + W + 20R ≤ S` satisfies `42·F ≤ S²`.

Proof of `42·F ≤ S²`: with `W ≤ S − 21D − 20R`,
`42·F ≤ S² − (S − 42D)² + 42·(41,935 − 36D)·R`.
* `D ≥ 1,165` (`36D ≥ 41,940`): the last term is `≤ 0`.
* `D ≤ 1,164`: `R ≤ 100,000`, so `42·41,935·R ≤ 176,127,000,000 ≤ (S − 42D)²` since
  `S − 42D ≥ 1,951,112`.
So the insertion cost is absorbed in the block envelope `⌊S²/42⌋ = 95,238,095,238`, and the
worst-case source clock with transitions is exactly `kPanCoupled`.
-/

namespace InitECandidate.Solver.GuestJointTransitionInsertionBound

open InitECandidate.Solver.GuestCoupledTxBlockStorageBound (kPanCoupled M)
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open InitECandidate.Solver.GuestSstoreCleanToDirtyTransition (kPanTransition)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Per-key linear insertion coefficient `5 · (8,388 − 1)`. -/
def kIns : Nat := 41935

/-- 1. Per-tx linear lemma: `20r ≤ M ⇒ 5·r(r−1) ≤ 41,935·r`. -/
theorem insert_linear (r : Nat) (h : 20 * r ≤ M) : 5 * (r * (r - 1)) ≤ kIns * r := by
  have hr : r - 1 ≤ 8387 := by unfold M at h; omega
  have : r * (r - 1) ≤ r * 8387 := Nat.mul_le_mul_left _ hr
  unfold kIns; rw [Nat.mul_comm 41935 r]; omega

/-- 2. Tightness of (1) at `r = 8,388`. -/
theorem insert_linear_tight : 20 * 8388 ≤ M ∧ 5 * (8388 * (8388 - 1)) = kIns * 8388 := by decide

/-- 3. Induction over the block's transactions: `Σ 5rᵢ(rᵢ−1) ≤ 41,935·R`. -/
theorem insert_sum (rs : List Nat) (h : ∀ r ∈ rs, 20 * r ≤ M) :
    (rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ kIns * rs.sum := by
  induction rs with
  | nil => simp
  | cons r t ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := insert_linear r (h r (by simp))
    have h2 := ih (fun x hx => h x (by simp [hx]))
    rw [Nat.mul_add]; omega

/-- 4. **Joint absorption**: `21D + W + 20R ≤ S ⇒ 42·(D(2W + 4R) + 41,935R) ≤ S²`. -/
theorem joint_transition_absorbed (D W R : Nat) (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R) + kIns * R) ≤ S * S := by
  have h' : (21 * (D : Int) + W + 20 * R) ≤ 2000000 := by unfold S at h; exact_mod_cast h
  have hD : (0 : Int) ≤ D := by positivity
  have hR : (0 : Int) ≤ R := by positivity
  have hW : (W : Int) ≤ 2000000 - 21 * D - 20 * R := by linarith
  have hm : (D : Int) * W ≤ D * (2000000 - 21 * D - 20 * R) := Int.mul_le_mul_of_nonneg_left hW hD
  have hsq : (0 : Int) ≤ (2000000 - 42 * (D : Int)) ^ 2 := sq_nonneg _
  have key : (42 : Int) * (D * (2 * W + 4 * R) + 41935 * R) ≤ 2000000 * 2000000 := by
    rcases Nat.lt_or_ge D 1165 with hlt | hge
    · have hDl : (D : Int) ≤ 1164 := by omega
      have hRl : (R : Int) ≤ 100000 := by linarith
      have hs : (1951112 : Int) ≤ 2000000 - 42 * D := by linarith
      have hs2 : (1951112 : Int) * 1951112 ≤ (2000000 - 42 * D) ^ 2 := by nlinarith
      nlinarith
    · have hDg : (1165 : Int) ≤ D := by exact_mod_cast hge
      have : (0 : Int) ≤ (36 * D - 41935) * R := mul_nonneg (by linarith) hR
      nlinarith
  unfold S kIns; exact_mod_cast key

/-- 5. Integer form: `D(2W + 4R) + 41,935R ≤ 95,238,095,238`. -/
theorem joint_le (D W R : Nat) (h : 21 * D + W + 20 * R ≤ S) :
    D * (2 * W + 4 * R) + kIns * R ≤ 95238095238 := by
  have := joint_transition_absorbed D W R h
  unfold S at this; omega

/-- 6. Attained exactly at `(D, W, R) = (47,619, 1,000,001, 0)`. -/
theorem joint_tight :
    21 * 47619 + 1000001 + 20 * 0 = S ∧
      47619 * (2 * 1000001 + 4 * 0) + kIns * 0 = 95238095238 := by decide

/-- 7. Pure-transition corner `D = 0`: `41,935 · 100,000 = 4,193,500,000` only. -/
theorem pure_transition_corner :
    21 * 0 + 0 + 20 * 100000 = S ∧ 0 * (2 * 0 + 4 * 100000) + kIns * 100000 = 4193500000 := by
  decide

/-- 8. Worst case with transitions equals `kPanCoupled` (block term unchanged, insertions absorbed). -/
theorem kPan_with_transitions (D W R : Nat) (h : 21 * D + W + 20 * R ≤ S) (Tloc : Nat)
    (hloc : Tloc ≤ 8 * 3994571428) :
    linear + Tloc + (D * (2 * W + 4 * R) + kIns * R) ≤ kPanCoupled := by
  have := joint_le D W R h
  unfold kPanCoupled; omega

/-- 9. Strict improvement over `kPanTransition` by exactly the former insertion term. -/
theorem improves_transition :
    kPanCoupled < kPanTransition ∧ kPanTransition - kPanCoupled = 4194300000 := by decide

/-- 10. Yukon margin at slope `6×` restored to `115,594,540,098`. -/
theorem margin6 : 6 * kPanCoupled < yukon ∧ yukon - 6 * kPanCoupled = 115594540098 := by decide

/-- 11. Exact slope threshold for the absorbed envelope: `k · kPanCoupled < Yukon ↔ k ≤ 6`. -/
theorem slope_threshold (k : Nat) : k * kPanCoupled < yukon ↔ k ≤ 6 :=
  InitECandidate.Solver.GuestCoupledTxBlockStorageBound.slope_threshold k

end InitECandidate.Solver.GuestJointTransitionInsertionBound
