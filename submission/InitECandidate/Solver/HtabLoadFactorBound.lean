set_option autoImplicit false

/-!
# `InitECandidate.Solver.HtabLoadFactorBound`

Model of the Guest open-addressing tables (`Guest/guest.pp.pnk`, `htab_*`).

Source facts modelled:
* `htab_set` grows (doubles `cap`) when `(count + 1) * 2 > cap`, then inserts.
  Hence the invariant `2 * count ≤ cap` (load factor ≤ 1/2) holds forever;
  `cap` is never a fixed 2048/8192.
* `htab_find_slot` / `htab_insert_raw` probe `i, i+1, … (mod cap)` until an
  unused slot; they terminate within `cap` probes iff some slot is unused.
* EIP-2929/2930: every new table key costs ≥ 1900 gas (cheapest: storage key in
  an access list), so a block with `gasLimit` gas creates ≤ `gasLimit / 1900` keys.
-/

namespace InitECandidate.Solver
namespace HtabLoadFactorBound

/-- Minimum gas per fresh key (EIP-2930 storage key in access list). -/
def minGasPerKey : Nat := 1900

/-- Block gas limit under study. -/
def blockGasLimit : Nat := 200000000

/-- Abstract table state: number of live keys and capacity. -/
structure Tab where
  count : Nat
  cap : Nat
deriving Repr

/-- `htab_set` on a fresh key: optional grow, then `htab_insert_raw`. -/
def setFresh (t : Tab) : Tab :=
  if (t.count + 1) * 2 > t.cap then ⟨t.count + 1, t.cap * 2⟩ else ⟨t.count + 1, t.cap⟩

/-- `n` successive fresh insertions. -/
def applyN : Nat → Tab → Tab
  | 0, t => t
  | n + 1, t => applyN n (setFresh t)

def Inv (t : Tab) : Prop := 2 ≤ t.cap ∧ 2 * t.count ≤ t.cap

/-- Load factor ≤ 1/2 is preserved by every fresh insertion. -/
theorem setFresh_inv (t : Tab) (h : Inv t) : Inv (setFresh t) := by
  unfold setFresh Inv at *
  split <;> simp <;> omega

/-- After any number of fresh insertions the invariant still holds. -/
theorem iterate_inv (t : Tab) (h : Inv t) : ∀ n, Inv (applyN n t) := by
  intro n
  induction n generalizing t with
  | zero => exact h
  | succ n ih => exact ih (setFresh t) (setFresh_inv t h)

/-- Invariant ⇒ strictly fewer used slots than capacity (an empty slot exists). -/
theorem count_lt_cap (t : Tab) (h : Inv t) : t.count < t.cap := by
  unfold Inv at h; omega

/-- Linear probe with explicit fuel: returns the number of probes used. -/
def probe (used : Nat → Bool) (cap start : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if used ((start) % cap) then
      (probe used cap (start + 1) fuel).map (· + 1)
    else some 0

theorem probe_some_of_free (used : Nat → Bool) (cap : Nat) (hcap : 0 < cap) :
    ∀ (k start : Nat), used ((start + k) % cap) = false →
      ∃ r, r ≤ k ∧ probe used cap start (k + 1) = some r := by
  intro k
  induction k with
  | zero =>
    intro start h
    refine ⟨0, Nat.le_refl _, ?_⟩
    simp [probe] at h ⊢; simp [h]
  | succ k ih =>
    intro start h
    by_cases hu : used (start % cap) = true
    · have h' : used ((start + 1 + k) % cap) = false := by
        rw [show start + 1 + k = start + (k + 1) by omega]; exact h
      obtain ⟨r, hr, hp⟩ := ih (start + 1) h'
      refine ⟨r + 1, by omega, ?_⟩
      rw [probe, if_pos hu, hp]; rfl
    · refine ⟨0, Nat.zero_le _, ?_⟩
      simp [probe] at hu ⊢; simp [hu]

/-- Probe bound: if some slot `j < cap` is free, a probe from any home slot
returns within `cap` probes (fuel `cap`, result `< cap`). -/
theorem htab_probe_terminates (used : Nat → Bool) (cap home j : Nat)
    (hj : j < cap) (hfree : used j = false) :
    ∃ r, r < cap ∧ probe used cap home cap = some r := by
  have hcap : 0 < cap := by omega
  let k := (j + cap - home % cap) % cap
  have hk : k < cap := Nat.mod_lt _ hcap
  have hidx : (home + k) % cap = j := by
    show (home + (j + cap - home % cap) % cap) % cap = j
    have h1 : home % cap < cap := Nat.mod_lt _ hcap
    have hd := Nat.mod_add_div home cap
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [show home + (j + cap - home % cap) = (j + cap) + cap * (home / cap) by omega,
      Nat.add_mul_mod_self_left, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  obtain ⟨r, hr, hp⟩ := probe_some_of_free used cap hcap k home (by rw [hidx]; exact hfree)
  -- extra fuel does not change a `some` result
  have mono : ∀ (f g s : Nat) (x : Nat), probe used cap s f = some x → probe used cap s (f + g) = some x := by
    intro f
    induction f with
    | zero => intro g s x h; simp [probe] at h
    | succ f ih =>
      intro g s x h
      rw [show f + 1 + g = (f + g) + 1 by omega]
      unfold probe at h ⊢
      split at h
      · rename_i hu; simp only [hu, if_true]
        cases hq : probe used cap (s + 1) f with
        | none => simp [hq] at h
        | some y => rw [hq] at h; rw [ih g (s+1) y hq]; exact h
      · rename_i hu; simp only [hu]; exact h
  refine ⟨r, by omega, ?_⟩
  have := mono (k + 1) (cap - (k + 1)) home r hp
  rwa [show k + 1 + (cap - (k + 1)) = cap by omega] at this

/-- Gas bound on fresh keys: `n` keys cost ≥ `1900 n` gas. -/
theorem keys_le_of_gas (n gas : Nat) (h : minGasPerKey * n ≤ gas) : n ≤ gas / minGasPerKey := by
  unfold minGasPerKey at *; omega

theorem keys_le_200M (n : Nat) (h : minGasPerKey * n ≤ blockGasLimit) : n ≤ 105263 := by
  unfold minGasPerKey blockGasLimit at h; omega

/-- Tightness: 105263 keys fit in 200M gas, 105264 do not. -/
theorem keys_bound_tight :
    minGasPerKey * 105263 ≤ blockGasLimit ∧ ¬ minGasPerKey * 105264 ≤ blockGasLimit := by
  decide

/-- A fixed (non-growing) table of `cap` slots would be exhausted by `cap` keys,
i.e. by only `1900 * cap` gas: 3,891,200 for 2048 slots, 15,564,800 for 8192. -/
theorem fixed_cap_threshold :
    minGasPerKey * 2048 = 3891200 ∧ minGasPerKey * 8192 = 15564800 ∧
    minGasPerKey * 2048 ≤ blockGasLimit ∧ minGasPerKey * 8192 ≤ blockGasLimit := by
  decide

/-- Main result: starting from a valid table (cap ≥ 2, load ≤ 1/2), after any
number `n` of gas-paid fresh insertions within the block limit, the table keeps
load ≤ 1/2, `n ≤ 105263`, and every lookup/insert probe returns in `< cap` steps. -/
theorem htab_probe_bound_of_gas_limit (t0 : Tab) (h0 : Inv t0) (n : Nat)
    (hgas : minGasPerKey * n ≤ blockGasLimit)
    (used : Nat → Bool) (home : Nat)
    (hfree : ∃ j, j < (applyN n t0).cap ∧ used j = false) :
    n ≤ 105263 ∧ Inv (applyN n t0) ∧
    (applyN n t0).count < (applyN n t0).cap ∧
    ∃ r, r < (applyN n t0).cap ∧
      probe used (applyN n t0).cap home (applyN n t0).cap = some r := by
  have hi := iterate_inv t0 h0 n
  obtain ⟨j, hj, hu⟩ := hfree
  exact ⟨keys_le_200M n hgas, hi, count_lt_cap _ hi, htab_probe_terminates used _ home j hj hu⟩

/-- Non-vacuity witness: the Guest's own initial shape (`htab_new(20, 16)`). -/
example : Inv ⟨0, 16⟩ := ⟨by decide, by decide⟩

/-- Non-vacuity of the main theorem's hypotheses (n = 105263, empty table). -/
example : minGasPerKey * 105263 ≤ blockGasLimit := keys_bound_tight.1

end HtabLoadFactorBound
end InitECandidate.Solver
