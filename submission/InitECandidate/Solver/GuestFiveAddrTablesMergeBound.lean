import InitECandidate.Solver.GuestMultiAddressMergeDominance

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestFiveAddrTablesMergeBound`

Quadratic absorption of the block address tables (`bs+8/16/24/40/48/72`) into the storage
envelope, by exact sum-of-squares identities.

With `X = D + A`, `Y = W + D + A`, `S = 2·10⁶`:
`S² − 40·(2XY + 5A²) = (S − 40X)² + 80X·(S − 21D − 27A − W) + 480DA + 280A²`
`S² − 40·(2XY + 12A²) = (S − 40X)² + 80X·(S − 21D − 27A − W) + 480DA`.
Coupled form (`21D + 26A + W ≤ S`): with `U = 21D + W`,
`84DW + 504A² ≤ U² + 504A² ≤ (U + 26A)² ≤ S²`.
-/

namespace InitECandidate.Solver.GuestFiveAddrTablesMergeBound

open InitECandidate.Solver.GuestBs32BlockStorageEnvelope (S)
open InitECandidate.Solver.GuestMultiAddressMergeDominance (kPanMultiAddrMerge)
open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

/-- 1. Exact identity (5 tables), over `Int`. -/
theorem identity5 (D A W : Int) :
    2000000 ^ 2 - 40 * (2 * (D + A) * (W + D + A) + 5 * A ^ 2) =
      (2000000 - 40 * (D + A)) ^ 2 + 80 * (D + A) * (2000000 - 21 * D - 27 * A - W)
        + 480 * D * A + 280 * A ^ 2 := by ring

/-- 2. **Five address tables absorbed**: `40·(2(D+A)(W+D+A) + 5A²) ≤ S²`. -/
theorem five_addr_tables_absorbed (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    40 * (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) ≤ S * S := by
  have h' : (21 * (D : Int) + 27 * A + W) ≤ 2000000 := by unfold S at h; push_cast; omega
  have hX : (0 : Int) ≤ D + A := by positivity
  have hr : (0 : Int) ≤ 80 * (D + A) * (2000000 - 21 * D - 27 * A - W) := by
    apply mul_nonneg; · positivity
    · linarith
  have hDA : (0 : Int) ≤ 480 * D * A := by positivity
  have hAA : (0 : Int) ≤ 280 * (A : Int) ^ 2 := by positivity
  have hs : (0 : Int) ≤ (2000000 - 40 * ((D : Int) + A)) ^ 2 := sq_nonneg _
  have key := identity5 D A W
  have : (40 : Int) * (2 * ((D + A) * (W + D + A)) + 5 * (A * A)) ≤ 2000000 * 2000000 := by
    nlinarith
  unfold S; exact_mod_cast this

/-- 3. Integer form `≤ 100,000,000,000`. -/
theorem five_le (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    2 * ((D + A) * (W + D + A)) + 5 * (A * A) ≤ 100000000000 := by
  have := five_addr_tables_absorbed D A W h
  unfold S at this; omega

/-- 4. Tight at `(D, W, A) = (50,000, 950,000, 0)`. -/
theorem five_tight :
    20 * 50000 + 26 * 0 + (950000 + 50000 + 0) = S ∧
      2 * ((50000 + 0) * (950000 + 50000 + 0)) + 5 * (0 * 0) = 100000000000 := by decide

/-- 5. Exact identity (12 tables): the `A²` slack is consumed, `480DA` remains. -/
theorem identity12 (D A W : Int) :
    2000000 ^ 2 - 40 * (2 * (D + A) * (W + D + A) + 12 * A ^ 2) =
      (2000000 - 40 * (D + A)) ^ 2 + 80 * (D + A) * (2000000 - 21 * D - 27 * A - W)
        + 480 * D * A := by ring

/-- 6. **Twelve address-table probes absorbed**: `40·(2(D+A)(W+D+A) + 12A²) ≤ S²`. -/
theorem twelve_addr_tables_absorbed (D A W : Nat) (h : 20 * D + 26 * A + (W + D + A) ≤ S) :
    40 * (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) ≤ S * S := by
  have h' : (21 * (D : Int) + 27 * A + W) ≤ 2000000 := by unfold S at h; push_cast; omega
  have hr : (0 : Int) ≤ 80 * (D + A) * (2000000 - 21 * D - 27 * A - W) := by
    apply mul_nonneg; · positivity
    · linarith
  have hDA : (0 : Int) ≤ 480 * D * A := by positivity
  have hs : (0 : Int) ≤ (2000000 - 40 * ((D : Int) + A)) ^ 2 := sq_nonneg _
  have key := identity12 D A W
  have : (40 : Int) * (2 * ((D + A) * (W + D + A)) + 12 * (A * A)) ≤ 2000000 * 2000000 := by
    nlinarith
  unfold S; exact_mod_cast this

/-- 7. Sharpness of the coefficient `12`: a second, pure-address vertex `(D, W, A) = (0, 650,000,
50,000)` on the budget line also reaches `100,000,000,000` (all residual terms vanish). -/
theorem twelve_sharp :
    20 * 0 + 26 * 50000 + (650000 + 0 + 50000) = S ∧
      2 * ((0 + 50000) * (650000 + 0 + 50000)) + 12 * (50000 * 50000) = 100000000000 := by
  decide

/-- 8. **Coupled** (`21D + 26A + W ≤ S`): `42·(2DW + 12A²) ≤ S²`. -/
theorem coupled_absorbed (D A W : Nat) (h : 21 * D + 26 * A + W ≤ S) :
    42 * (2 * (D * W) + 12 * (A * A)) ≤ S * S := by
  have h' : (21 * (D : Int) + 26 * A + W) ≤ 2000000 := by unfold S at h; exact_mod_cast h
  have hU : (0 : Int) ≤ 21 * D + W := by positivity
  have hA : (0 : Int) ≤ A := by positivity
  have e1 : (84 : Int) * (D * W) ≤ (21 * D + W) ^ 2 := by nlinarith [sq_nonneg ((21 : Int) * D - W)]
  have e2 : (21 * (D : Int) + W) ^ 2 + 504 * A ^ 2 ≤ (21 * D + W + 26 * A) ^ 2 := by nlinarith
  have hT : (0 : Int) ≤ 21 * D + W + 26 * A := by positivity
  have e3 : (21 * (D : Int) + W + 26 * A) ^ 2 ≤ 2000000 ^ 2 := pow_le_pow_left₀ hT (by linarith) 2
  have : (42 : Int) * (2 * (D * W) + 12 * (A * A)) ≤ 2000000 * 2000000 := by nlinarith
  unfold S; exact_mod_cast this

/-- 9. Coupled integer form `≤ 95,238,095,238`, tight at `(47,619, 1,000,001, 0)`. -/
theorem coupled_le (D A W : Nat) (h : 21 * D + 26 * A + W ≤ S) :
    2 * (D * W) + 12 * (A * A) ≤ 95238095238 ∧
      2 * (47619 * 1000001) + 12 * (0 * 0) = 95238095238 := by
  have := coupled_absorbed D A W h
  unfold S at this; constructor <;> omega

/-- 10. Pure-address corner of the coupled form: `A = 76,923` gives only `71,005,775,148`. -/
theorem coupled_addr_corner :
    21 * 0 + 26 * 76923 + 0 ≤ S ∧ 2 * (0 * 0) + 12 * (76923 * 76923) = 71005775148 ∧
      71005775148 < 95238095238 := by decide

/-- 11. The source envelope is unchanged and the `6×` slope still passes Yukon. -/
theorem envelope_unchanged : 6 * kPanMultiAddrMerge < yukon ∧ kPanMultiAddrMerge = 136116135658 := by
  decide

end InitECandidate.Solver.GuestFiveAddrTablesMergeBound
