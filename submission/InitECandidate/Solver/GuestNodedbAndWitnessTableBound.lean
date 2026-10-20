import InitECandidate.Solver.GuestTransientStorageSubcallRevertAndAbsorption

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestNodedbAndWitnessTableBound`

Hand transcription of `guest.pp.pnk` (wt-2).

* `input_blob` (l.272): `len ≤ 134,217,712` (`maxInputBytes`), else `trap_with(8)`.
* Witness decode (l.~3015–3040): `decode_bytes_list(…, maxb = 1024)` for state nodes (`si+40/48`),
  `maxb = 65,536` for code (`si+56/64`). An SSZ variable list spends a 4-byte offset per element,
  so `n ≤ len / 4 = 33,554,428` entries (empty slices allowed: minimal node = 0 payload bytes).
* `nodedb_build` (l.3691): `cap` = least power of two `≥ 2n + 2` (≥ 4), `htab_new(32, cap)`, then
  for each slice `keccak256` + `htab_set(t, hash, slice)`. Load `≤ 1/2`, no `htab_grow`.
  Called twice (l.15578 state, l.15579 code).
* `nodedb_lookup` (l.3705): one `htab_get` = one `htab_find_slot`; callers: witness decode
  (l.3769, 3959), code fetch (l.5585), `mpt_from_witness` in `compute_state_root` (l.14678/14710).

Keys are Keccak-256 outputs, not attacker-chosen bytes: forcing `htab_hash` collisions needs a
search over node contents (`≈ cap` Keccak trials per colliding node). Bound below:
* worst case (every key in one run, adversary able to grind): `Σ_{i<n} 2i = n(n−1)` ticks per build
  — independent of gas, bounded only by input size.
* without forced collisions (run length `≤ r`): `2 r n` ticks.
-/

namespace InitECandidate.Solver.GuestNodedbAndWitnessTableBound

open InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)

def maxInput : Nat := 134217712

/-- Capacity chosen by `nodedb_build`: least power of two `≥ 2n + 2`, starting at 4. -/
def capLoop : Nat → Nat → Nat → Nat
  | 0, c, _ => c
  | f + 1, c, n => if c < 2 * n + 2 then capLoop f (2 * c) n else c

def capOf (n : Nat) : Nat := capLoop 64 4 n

/-- 1. Entry count from the SSZ offsets: `n ≤ 33,554,428`, tight. -/
theorem entries_le (n : Nat) (h : 4 * n ≤ maxInput) : n ≤ 33554428 := by
  unfold maxInput at h; omega

theorem entries_tight : 4 * 33554428 = maxInput := by decide

/-- 2. Capacity at the extreme: `2²⁶ = 67,108,864 ≥ 2n + 2`, and half of it is too small. -/
theorem cap_extreme : 2 * 33554428 + 2 ≤ 67108864 ∧ 33554432 < 2 * 33554428 + 2 := by decide

/-- 3. Load factor `≤ 1/2`: no `htab_grow` during the build. -/
theorem load_half (n : Nat) (c : Nat) (hc : 2 * n + 2 ≤ c) : (n + 1) * 2 ≤ c := by omega

/-- 4. Small cases of `capOf`. -/
theorem cap_small : capOf 0 = 4 ∧ capOf 1 = 4 ∧ capOf 2 = 8 ∧ capOf 7 = 16 := by simp [capOf, capLoop]

/-- Build probe ticks with all keys in one run (2 ticks per probed entry). -/
def worstBuild (n : Nat) : Nat := n * (n - 1)

/-- Build probe ticks when every run is `≤ r`. -/
def boundedBuild (r n : Nat) : Nat := 2 * r * n

/-- 5. Adversarial worst case at the input cap exceeds Yukon by orders of magnitude. -/
theorem worst_build_val : worstBuild 33554428 = 1125899604852756 ∧ yukon < worstBuild 33554428 := by
  decide

/-- 6. With bounded runs the build is linear: `r = 8` gives `536,870,848` ticks. -/
theorem bounded_build_val : boundedBuild 8 33554428 = 536870848 ∧ boundedBuild 8 33554428 < yukon := by
  decide

/-- 7. Run-length threshold for the build alone to stay under Yukon: `r ≤ 13,421`. -/
theorem run_threshold :
    boundedBuild 13421 33554428 < yukon ∧ yukon < boundedBuild 13422 33554428 := by decide

/-- 8. Monotonicity in the entry count. -/
theorem bounded_mono (r a b : Nat) (h : a ≤ b) : boundedBuild r a ≤ boundedBuild r b := by
  unfold boundedBuild; exact Nat.mul_le_mul_left _ h

/-- 9. Grinding cost: forcing one more collision needs `≈ cap = 2²⁶` Keccak trials; the full worst
case needs `≥ n · 2²⁶ / 2` trials ≈ `1.1 · 10¹⁵`. -/
theorem grind_cost : 33554428 * 67108864 / 2 = 1125899772624896 := by decide

/-- 10. Two builds (state + code) share the input: `n_s + n_c ≤ 33,554,428`, so the bounded total
is still `≤ 2 r · 33,554,428`. -/
theorem two_builds (r ns nc : Nat) (h : 4 * (ns + nc) ≤ maxInput) :
    boundedBuild r ns + boundedBuild r nc ≤ boundedBuild r 33554428 := by
  unfold boundedBuild maxInput at *
  have : ns + nc ≤ 33554428 := by omega
  have := Nat.mul_le_mul_left (2 * r) this
  rw [Nat.mul_add] at this; exact this

end InitECandidate.Solver.GuestNodedbAndWitnessTableBound
