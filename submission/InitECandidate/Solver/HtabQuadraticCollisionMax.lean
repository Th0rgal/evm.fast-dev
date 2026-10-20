import InitECandidate.Solver.GuestEvmStepOpcodeBounds

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.HtabQuadraticCollisionMax`

Exact integer maximum of the collision-probe product under a 200M gas block.

Gas split: `c` colliding fresh keys at `g_c ≥ 1900` (access list) or `≥ 2100` (cold `SLOAD`),
`w` warm lookups at `g_w ≥ 100`. Dividing by 100: `19c + w ≤ 2·10⁶` (resp. `21c + w ≤ 2·10⁶`).
Completing the square with `x = 19c` (resp. `21c`):
`19·c·w ≤ x·(2·10⁶ − x) = 10¹² − (x − 10⁶)²`, and `x` is a multiple of 19 (resp. 21), so
`|x − 10⁶| ≥ 8` (resp. `≥ 1`). Exact maxima:
* cold `SLOAD`: `c·w ≤ 47,619,047,619`, attained at `(47,619, 1,000,001)`;
* access list: `c·w ≤ 52,631,578,944`, attained at `(52,632, 999,992)` — **not** at
  `(52,631, 1,000,011)`, which gives `52,631,578,941`.

Source clock model (stated, not derived from `PanSem`): `k_pan ≤ prologue + 18·G + p·c·(w + c)`
with `p` ticks per probe (warm scans `c·w` plus insertion scans `≤ c²`). With `p = 2` (one scan
per access: loop iteration + `memeq` call) this gives `k_pan ≤ 114,770,675,338 < 115·10⁹`.
If an access scans several colliding tables (`is_warm_storage_key`, then `get_storage`'s
`htab_set`/`stor_lookup`), `p` grows linearly; the bound is given for general `p`.
-/

namespace InitECandidate.Solver.HtabQuadraticCollisionMax

open InitECandidate.Solver.GuestEvmStepOpcodeBounds

/-- 3. Cold-`SLOAD` maximum by completing the square. -/
theorem cw_le_cold (c w : Nat) (h : 21 * c + w ≤ 2000000) : c * w ≤ 47619047619 := by
  have hw : (w : Int) ≤ 2000000 - 21 * c := by omega
  have hc0 : (0 : Int) ≤ c := by omega
  have hmul : (c : Int) * w ≤ c * (2000000 - 21 * c) := Int.mul_le_mul_of_nonneg_left hw hc0
  have hsq : (1 : Int) ≤ (21 * (c : Int) - 1000000) ^ 2 := by
    rcases Nat.lt_or_ge c 47620 with hlt | hge
    · have : (21 * (c : Int) - 1000000) ≤ -1 := by omega
      nlinarith
    · have : (20 : Int) ≤ 21 * (c : Int) - 1000000 := by omega
      nlinarith
  have : (21 : Int) * (c * w) ≤ 999999999999 := by nlinarith
  have : ((c * w : Nat) : Int) ≤ 47619047619 := by push_cast; omega
  omega

/-- 4. The cold-`SLOAD` maximum is attained at `(47,619, 1,000,001)`, exactly 200M gas. -/
theorem cw_cold_attained :
    21 * 47619 + 1000001 = 2000000 ∧ 47619 * 1000001 = 47619047619 ∧
      47619 * 2100 + 1000001 * 100 = gasCap := by decide

/-- 5. Access-list maximum by completing the square (`|19c − 10⁶| ≥ 8`). -/
theorem cw_le_al (c w : Nat) (h : 19 * c + w ≤ 2000000) : c * w ≤ 52631578944 := by
  have hw : (w : Int) ≤ 2000000 - 19 * c := by omega
  have hc0 : (0 : Int) ≤ c := by omega
  have hmul : (c : Int) * w ≤ c * (2000000 - 19 * c) := Int.mul_le_mul_of_nonneg_left hw hc0
  have hsq : (64 : Int) ≤ (19 * (c : Int) - 1000000) ^ 2 := by
    rcases Nat.lt_or_ge c 52632 with hlt | hge
    · have : (19 * (c : Int) - 1000000) ≤ -11 := by omega
      nlinarith
    · have : (8 : Int) ≤ 19 * (c : Int) - 1000000 := by omega
      nlinarith
  have : (19 : Int) * (c * w) ≤ 999999999936 := by nlinarith
  have : ((c * w : Nat) : Int) ≤ 52631578944 := by push_cast; omega
  omega

/-- 6. Attained at `(52,632, 999,992)` (exactly 200M gas). -/
theorem cw_al_attained :
    19 * 52632 + 999992 = 2000000 ∧ 52632 * 999992 = 52631578944 ∧
      52632 * 1900 + 999992 * 100 = gasCap := by decide

/-- 7. Correction: `(52,631, 1,000,011)` is feasible but strictly below the maximum. -/
theorem al_neighbour_not_max :
    19 * 52631 + 1000011 = 2000000 ∧ 52631 * 1000011 = 52631578941 ∧
      52631 * 1000011 < 52632 * 999992 := by decide

/-- 8. Unconditional form over gas prices: any split within 200M has `c·w ≤ 52,631,578,944`,
and `≤ 47,619,047,619` when fresh keys cost `≥ 2100`. -/
theorem cw_le_general (c w gc gw : Nat) (hw : 100 ≤ gw) (hG : c * gc + w * gw ≤ gasCap) :
    (1900 ≤ gc → c * w ≤ 52631578944) ∧ (2100 ≤ gc → c * w ≤ 47619047619) := by
  have h2 : w * 100 ≤ w * gw := Nat.mul_le_mul_left _ hw
  unfold gasCap at hG
  refine ⟨fun hc => cw_le_al c w ?_, fun hc => cw_le_cold c w ?_⟩
  · have h1 : c * 1900 ≤ c * gc := Nat.mul_le_mul_left _ hc
    omega
  · have h1 : c * 2100 ≤ c * gc := Nat.mul_le_mul_left _ hc
    omega

/-- 9. Warm + insertion probes: `c·(w + c) ≤ 55,555,555,552` (`|18c − 10⁶| ≥ 8`). -/
theorem probes_le (c w : Nat) (h : 19 * c + w ≤ 2000000) : c * (w + c) ≤ 55555555552 := by
  have hw : (w : Int) + c ≤ 2000000 - 18 * c := by omega
  have hc0 : (0 : Int) ≤ c := by omega
  have hmul : (c : Int) * (w + c) ≤ c * (2000000 - 18 * c) := Int.mul_le_mul_of_nonneg_left hw hc0
  have hsq : (64 : Int) ≤ (18 * (c : Int) - 1000000) ^ 2 := by
    rcases Nat.lt_or_ge c 55556 with hlt | hge
    · have : (18 * (c : Int) - 1000000) ≤ -10 := by omega
      nlinarith
    · have : (8 : Int) ≤ 18 * (c : Int) - 1000000 := by omega
      nlinarith
  have : (18 : Int) * (c * (w + c)) ≤ 999999999936 := by nlinarith
  have : ((c * (w + c) : Nat) : Int) ≤ 55555555552 := by push_cast; omega
  omega

/-- 10. Tightness of (9) at `(55,556, 944,436)`. -/
theorem probes_attained :
    19 * 55556 + 944436 = 2000000 ∧ 55556 * (944436 + 55556) = 55555555552 := by decide

/-- Source clock model with `p` ticks per probe. -/
def kPanModel (p c w : Nat) : Nat :=
  SelfContainedMasterK.prologueTicks + 18 * gasCap + p * (c * (w + c))

/-- 11. With `p = 2`: `k_pan ≤ 114,770,675,338 < 115·10⁹` for every gas-feasible split,
attained at `(55,556, 944,436)`. -/
theorem kPan_le (c w : Nat) (h : 19 * c + w ≤ 2000000) :
    kPanModel 2 c w ≤ 114770675338 ∧ kPanModel 2 55556 944436 = 114770675338 ∧
      114770675338 < 115000000000 := by
  have hp := probes_le c w h
  refine ⟨?_, by decide, by decide⟩
  unfold kPanModel SelfContainedMasterK.prologueTicks gasCap; omega

/-- 12. General `p`: the worst case exceeds `maxGuestSourceClock` for every `p ≥ 1`, and stays
below the Yukon ceiling `900,719,925,474` iff `p ≤ 16`. -/
theorem kPan_general (p : Nat) :
    (1 ≤ p → maxGuestSourceClock < kPanModel p 55556 944436) ∧
      (kPanModel p 55556 944436 < 900719925474 ↔ p ≤ 16) := by
  unfold kPanModel SelfContainedMasterK.prologueTicks gasCap maxGuestSourceClock
  constructor
  · intro hp; omega
  · omega

end InitECandidate.Solver.HtabQuadraticCollisionMax
