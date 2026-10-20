import InitECandidate.Solver.GuestFiveAddrTablesMergeBound

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

/-!
# `InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope`

One master inequality over `(D, R, A, C, W)` for all block hash tables
(`bs+32`, `ts+32`, `bs+72`, `bs+8/16/24/40/48`) under the unified budget
`21D + 20R + 26A + 21C + W ≤ S`, `S = 2·10⁶`.

Coupled envelope, proof route (no vertex case split; the hint `T = S − 26A − 21C` route fails for
small `T`, since `42·41,935·R ≤ (20R)²` is false for `R < 4,403`):
with `V = 21D + 26A + 21C + W` and `V + 20R ≤ S`,
* `S² ≥ S·(V + 20R) ≥ V² + 40,000,000·R`;
* `V² ≥ 84DW + 42CW + 441C² + 676A²` (cross terms ≥ 0);
* `42·4DR ≤ 16,000,000·R` since `D ≤ 95,238`, and `42·41,935 = 1,761,270 ≤ 24,000,000`.

Merge envelope: with `X = D + R + A`, `Y = W + X`, `V₀ = 20X + 6A + Y`, exact identity
`V₀² − 40(2XY + 12A²) = (20X − Y − 6A)² + 480A(X − A)`, and `X ≥ A`; the `C` term is absorbed by
`(V₀ + 21C)² ≥ V₀² + 42CV₀ + 441C²` with `V₀ ≥ Y`.
-/

namespace InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope

open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S linear)
open InitECandidate.Solver.GuestMergeTxUnionEnvelope (kPanMerge locCoup mergeLin)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- Coupled objective. -/
def F (D R A C W : Nat) : Nat := D * (2 * W + 4 * R) + 41935 * R + 12 * (A * A) + C * (W + C)

/-- 1. **Unified 5-variable coupled envelope**: `42·F ≤ S²`. -/
theorem unified_five_var_coupled_envelope (D R A C W : Nat)
    (h : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S) : 42 * F D R A C W ≤ S * S := by
  unfold F
  have h' : (21 * (D : Int) + 20 * R + 26 * A + 21 * C + W) ≤ 2000000 := by
    unfold S at h; exact_mod_cast h
  have hD0 : (0 : Int) ≤ D := by positivity
  have hR0 : (0 : Int) ≤ R := by positivity
  have hA0 : (0 : Int) ≤ A := by positivity
  have hC0 : (0 : Int) ≤ C := by positivity
  have hW0 : (0 : Int) ≤ W := by positivity
  set V : Int := 21 * D + 26 * A + 21 * C + W with hV
  have hV0 : 0 ≤ V := by positivity
  have hDle : (D : Int) ≤ 95238 := by omega
  -- S² ≥ S(V+20R) ≥ V² + 40·10⁶·R
  have s1 : (2000000 : Int) * 2000000 ≥ 2000000 * (V + 20 * R) := by nlinarith
  have s2 : (2000000 : Int) * V ≥ V * V := by nlinarith
  -- V² lower bound
  have v1 : (84 : Int) * (D * W) ≤ (21 * D + W) ^ 2 := by nlinarith [sq_nonneg ((21 : Int) * D - W)]
  have v2 : (84 : Int) * (D * W) + 42 * (C * W) + 441 * (C * C) + 504 * (A * A) ≤ V * V := by
    rw [hV]; nlinarith [mul_nonneg hA0 hD0, mul_nonneg hA0 hC0, mul_nonneg hA0 hW0,
      mul_nonneg hC0 hD0, mul_nonneg hA0 hA0]
  have r1 : (168 : Int) * (D * R) ≤ 16000000 * R := by nlinarith
  have : (42 : Int) * (D * (2 * W + 4 * R) + 41935 * R + 12 * (A * A) + C * (W + C))
      ≤ 2000000 * 2000000 := by nlinarith [mul_nonneg hC0 hC0]
  unfold S; exact_mod_cast this

/-- 2. Integer form `F ≤ 95,238,095,238`. -/
theorem unified_coupled_le (D R A C W : Nat) (h : 21 * D + 20 * R + 26 * A + 21 * C + W ≤ S) :
    F D R A C W ≤ 95238095238 := by
  have := unified_five_var_coupled_envelope D R A C W h
  unfold S at this; omega

/-- 3. Attained at `(D, R, A, C, W) = (47,619, 0, 0, 0, 1,000,001)`. -/
theorem unified_coupled_tight :
    21 * 47619 + 20 * 0 + 26 * 0 + 21 * 0 + 1000001 = S ∧ F 47619 0 0 0 1000001 = 95238095238 := by
  decide

/-- 4. Pure-`bs+72` corner (`C = 95,238`) is far below. -/
theorem unified_cold_corner : F 0 0 0 95238 0 = 9070276644 ∧ 9070276644 < 95238095238 := by decide

/-- Merge objective (`X = D + R + A`, `Y = W + X`). -/
def G (D R A C W : Nat) : Nat :=
  2 * ((D + R + A) * (W + (D + R + A))) + 12 * (A * A) + C * ((W + (D + R + A)) + C)

/-- 5. Exact identity behind the merge envelope. -/
theorem merge_identity (X Y A : Int) :
    (20 * X + 6 * A + Y) ^ 2 - 40 * (2 * X * Y + 12 * A ^ 2) = (20 * X - Y - 6 * A) ^ 2 + 480 * A * (X - A) := by
  ring

/-- 6. **Unified 5-variable merge envelope**: `40·G ≤ S²` under `20X + 6A + 21C + Y ≤ S`. -/
theorem unified_five_var_merge_envelope (D R A C W : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S) : 40 * G D R A C W ≤ S * S := by
  unfold G
  have h' : (20 * ((D : Int) + R + A) + 6 * A + 21 * C + (W + (D + R + A))) ≤ 2000000 := by
    unfold S at h; exact_mod_cast h
  have hD0 : (0 : Int) ≤ D := by positivity
  have hR0 : (0 : Int) ≤ R := by positivity
  have hA0 : (0 : Int) ≤ A := by positivity
  have hC0 : (0 : Int) ≤ C := by positivity
  have hW0 : (0 : Int) ≤ W := by positivity
  set X : Int := D + R + A with hX
  set Y : Int := W + X with hY
  have hXA : 0 ≤ X - A := by rw [hX]; linarith
  have id := merge_identity X Y A
  have e1 : (40 : Int) * (2 * X * Y + 12 * A ^ 2) ≤ (20 * X + 6 * A + Y) ^ 2 := by
    nlinarith [sq_nonneg (20 * X - Y - 6 * A), mul_nonneg hA0 hXA]
  set V0 : Int := 20 * X + 6 * A + Y with hV0
  have hV0Y : Y ≤ V0 := by rw [hV0]; nlinarith
  have hY0 : 0 ≤ Y := by rw [hY, hX]; positivity
  have e2 : (40 : Int) * (C * (Y + C)) ≤ 42 * C * V0 + 441 * (C * C) := by nlinarith
  have hT : (0 : Int) ≤ V0 + 21 * C := by nlinarith
  have e3 : (V0 + 21 * C) ^ 2 ≤ (2000000 : Int) ^ 2 := pow_le_pow_left₀ hT (by linarith) 2
  have fin : (40 : Int) * (2 * (X * Y) + 12 * (A * A) + C * (Y + C)) ≤ 2000000 * 2000000 := by
    nlinarith
  rw [hY, hX] at fin
  unfold S
  have : ((40 * (2 * ((D + R + A) * (W + (D + R + A))) + 12 * (A * A) + C * (W + (D + R + A) + C)) : Nat) : Int)
      ≤ ((2000000 * 2000000 : Nat) : Int) := by push_cast; linarith
  exact_mod_cast this

/-- 7. Integer form `G ≤ 100,000,000,000`. -/
theorem unified_merge_le (D R A C W : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S) :
    G D R A C W ≤ 100000000000 := by
  have := unified_five_var_merge_envelope D R A C W h
  unfold S at this; omega

/-- 8. Attained at `(50,000, 0, 0, 0, 950,000)`, and on the face `D + R = 50,000` (e.g. `R = 48,000`). -/
theorem unified_merge_tight :
    G 50000 0 0 0 950000 = 100000000000 ∧ G 2000 48000 0 0 950000 = 100000000000 ∧
      20 * (2000 + 48000 + 0) + 6 * 0 + 21 * 0 + (950000 + (2000 + 48000 + 0)) = S := by decide

/-- Unified all-tables source clock. -/
def kPanUnifiedAllTables : Nat := linear + locCoup + 100000000000 + mergeLin

/-- 9. Value, equal to `kPanMerge`. -/
theorem kPanUnified_val : kPanUnifiedAllTables = 136116135658 ∧ kPanUnifiedAllTables = kPanMerge := by
  decide

/-- 10. Master: every feasible `(D, R, A, C, W)` with local/linear terms stays under it. -/
theorem kPanUnified_master (D R A C W Tloc Tlin : Nat)
    (h : 20 * (D + R + A) + 6 * A + 21 * C + (W + (D + R + A)) ≤ S)
    (hloc : Tloc ≤ locCoup) (hlin : Tlin ≤ mergeLin) :
    linear + Tloc + G D R A C W + Tlin ≤ kPanUnifiedAllTables := by
  have := unified_merge_le D R A C W h
  unfold kPanUnifiedAllTables; omega

/-- 11. Slopes `3×–6×` pass Yukon; exact threshold `k ≤ 6`. -/
theorem slopes (k : Nat) :
    6 * kPanUnifiedAllTables < yukon ∧ (k * kPanUnifiedAllTables < yukon ↔ k ≤ 6) := by
  refine ⟨by decide, ?_⟩
  unfold kPanUnifiedAllTables linear locCoup mergeLin yukon; omega

end InitECandidate.Solver.GuestUnifiedAllTablesMasterEnvelope
