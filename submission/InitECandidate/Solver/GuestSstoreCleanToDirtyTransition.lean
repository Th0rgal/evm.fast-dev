import InitECandidate.Solver.GuestSstoreWarmCoeffAudit

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestSstoreCleanToDirtyTransition`

Clean→dirty transition of a warm `op_sstore` (hand transcription, `guest.pp.pnk` wt-2).

* A *clean* warm `SSTORE` on key `k` (warm, not in `ts+32`) does `(5 local, 2 block)` finds
  (`GuestSstoreWarmCoeffAudit.sstore_clean_counts`), then `set_storage`→`jset` inserts `k` in
  `ts+32`: every later `SSTORE`/`SLOAD` on `k` in the same tx is dirty `(5, 1)`.
* `ev+176` is per-tx, so a clean op in tx `i` needs `k` warmed in tx `i` first: ≥ 19 units
  (access list) or 21 (cold), plus 1 for the `SSTORE`. Each clean op therefore consumes ≥ 20 units
  *of its own* and happens at most once per (key, tx).
* Clean op `jset` inserts grow the inner `ts+32` cluster: the `t`-th clean insert in tx `i` scans
  `≤ t` slots in 2 finds + 1 insert-scan; charged here as `10·t` (5 finds × 2 ticks).

Block term: per-op block ticks `≤ D·(2W + 4R)` under `21D + W + 20R ≤ S`. Since
`4R ≤ 2·20R`, the transitions **do not raise** the block maximum `S²/42`.
Local insertion term: `Σᵢ 5·rᵢ(rᵢ−1) ≤ 5·(M/20)·Σ rᵢ ≤ 5·M·S/400 = 4,194,300,000`.
-/

namespace InitECandidate.Solver.GuestSstoreCleanToDirtyTransition

open InitECandidate.Solver.GuestSstoreWarmCoeffAudit (Tab sstoreWarm cnt)
open InitECandidate.Solver.GuestCoupledTxBlockStorageBound (kPanCoupled M)
open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Dirty flag after `set_storage` (always sets the key in `ts+32`). -/
def afterSet (_ : Bool) : Bool := true

/-- Block finds of `n` successive `SSTORE`s on one key in one tx, starting from `dirty`. -/
def seqBlock : Bool → Nat → Nat
  | _, 0 => 0
  | d, n + 1 => cnt .blockStor (sstoreWarm d) + seqBlock (afterSet d) n

/-- Minimal units of a clean warm `SSTORE` (warming ≥ 19 + op 1). -/
def cleanUnits : Nat := 19 + 1

/-- Transition envelope. -/
def kPanTransition : Nat := kPanCoupled + 4194300000

/-- 1. Transition: after any `SSTORE` the key is dirty, and a dirty op has 1 block find. -/
theorem transition (d : Bool) :
    afterSet d = true ∧ cnt .blockStor (sstoreWarm (afterSet d)) = 1 ∧
      cnt .blockStor (sstoreWarm false) = 2 := by
  cases d <;> decide

/-- 2. Exact block finds of a sequence: `n + 1` if it starts clean, `n` if dirty (`n ≥ 1`). -/
theorem seqBlock_eq (n : Nat) : seqBlock false (n + 1) = n + 2 ∧ seqBlock true n = n := by
  have hd : ∀ k, seqBlock true k = k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih =>
      have h1 : cnt .blockStor (sstoreWarm true) = 1 := by decide
      simp only [seqBlock, afterSet, ih, h1]; omega
  refine ⟨?_, hd n⟩
  simp only [seqBlock, afterSet, hd]
  have : cnt .blockStor (sstoreWarm false) = 2 := by decide
  omega

/-- 3. Clean ops are expensive: `cleanUnits = 20 ≥ 21 − 1`, and per-unit block ticks of a clean op
(4) are below those of a dirty probe (2 per unit) times 20. -/
theorem clean_cost : cleanUnits = 20 ∧ 4 ≤ 2 * cleanUnits := by decide

/-- 4. **Block term with transitions**: `21D + W + 20R ≤ S ⇒ 42·D·(2W + 4R) ≤ S²`. -/
theorem block_with_clean (D W R : Nat) (h : 21 * D + W + 20 * R ≤ S) :
    42 * (D * (2 * W + 4 * R)) ≤ S * S := by
  have h' : (21 * (D : Int) + W + 20 * R) ≤ 2000000 := by unfold S at h; exact_mod_cast h
  have hD : (0 : Int) ≤ D := by positivity
  have hR : (0 : Int) ≤ R := by positivity
  have hX : (2 * (W : Int) + 4 * R) ≤ 2 * (2000000 - 21 * D) := by linarith
  have hm : (D : Int) * (2 * W + 4 * R) ≤ D * (2 * (2000000 - 21 * D)) :=
    Int.mul_le_mul_of_nonneg_left hX hD
  have hsq : (0 : Int) ≤ (2000000 - 42 * (D : Int)) ^ 2 := sq_nonneg _
  have : (42 : Int) * (D * (2 * W + 4 * R)) ≤ 2000000 * 2000000 := by nlinarith
  unfold S; exact_mod_cast this

/-- 5. Hence block ticks `≤ 95,238,095,238`, unchanged; tight at `R = 0`, `(47619, 1000001)`. -/
theorem block_unchanged (D W R : Nat) (h : 21 * D + W + 20 * R ≤ S) :
    D * (2 * W + 4 * R) ≤ 95238095238 ∧ 47619 * (2 * 1000001 + 4 * 0) = 95238095238 := by
  have := block_with_clean D W R h
  unfold S at this; constructor <;> omega

/-- 6. Per-tx insertion: `20 r ≤ m ≤ M ⇒ 400·r·(r−1) ≤ 20·M·r`... summed: `80·Σ 5rᵢ(rᵢ−1) ≤ M·Σ 20rᵢ`. -/
theorem insert_list (rs : List Nat) (h : ∀ r ∈ rs, 20 * r ≤ M) :
    20 * (rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ 5 * M * rs.sum := by
  induction rs with
  | nil => simp
  | cons r t ih =>
    simp only [List.map_cons, List.sum_cons]
    have hr := h r (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    have h1 : r * (r - 1) ≤ r * r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have h2 : 20 * r * r ≤ M * r := Nat.mul_le_mul_right _ hr
    rw [Nat.mul_add, Nat.mul_add]
    have : 20 * (5 * (r * (r - 1))) ≤ 5 * (M * r) := by
      have : 20 * (r * r) = 20 * r * r := by ring
      omega
    have e : 5 * M * r = 5 * (M * r) := by ring
    omega

/-- 7. With `20·Σ rᵢ ≤ S`: insertion ticks `≤ 4,194,300,000`. -/
theorem insert_le (rs : List Nat) (h : ∀ r ∈ rs, 20 * r ≤ M) (hS : 20 * rs.sum ≤ S) :
    (rs.map (fun r => 5 * (r * (r - 1)))).sum ≤ 4194300000 := by
  have := insert_list rs h
  unfold M S at *; omega

/-- 8. Tightness of (7) per tx: `r = 8388` saturates `20r ≤ M`, with `5r(r−1) = 351,750,780`. -/
theorem insert_tight : 20 * 8388 ≤ M ∧ M < 20 * 8389 ∧ 5 * (8388 * (8388 - 1)) = 351750780 := by
  decide

/-- 9. Master value: `kPanTransition = 135,048,530,896`, exceeding `kPanCoupled` by exactly the
insertion term. -/
theorem kPanTransition_val :
    kPanTransition = 135048530896 ∧ kPanTransition - kPanCoupled = 4194300000 := by decide

/-- 10. Target slopes `3×, 4×, 5×, 6×` all stay under Yukon. -/
theorem slopes_ok :
    3 * kPanTransition < yukon ∧ 4 * kPanTransition < yukon ∧
      5 * kPanTransition < yukon ∧ 6 * kPanTransition < yukon := by decide

/-- 11. Exact threshold: `k · kPanTransition < Yukon ↔ k ≤ 6`. -/
theorem slope_threshold (k : Nat) : k * kPanTransition < yukon ↔ k ≤ 6 := by
  unfold kPanTransition kPanCoupled
    InitECandidate.Solver.GuestBs32BlockStorageEnvelope.linear yukon
  omega

/-- 12. Yukon margin at `6×`. -/
theorem margin6 : yukon - 6 * kPanTransition = 90428740098 := by decide

end InitECandidate.Solver.GuestSstoreCleanToDirtyTransition
