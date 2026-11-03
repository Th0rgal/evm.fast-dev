import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.U256Half
import Mathlib.Data.Nat.Size

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith

/-- Odd/odd subtraction makes an even operand, accounting for an iteration
which need not immediately reduce either operand's bit length. -/
def inverseRank (u v : Nat) : Nat :=
  2 * (u.size + v.size) + if u % 2 = 1 ∧ v % 2 = 1 then 1 else 0

def inverseSubtract (u v : Nat) : Nat × Nat :=
  if v ≤ u then (u - v, v) else (u, v - u)

theorem inverseRank_bound {u v width : Nat}
    (hu : u < 2 ^ width) (hv : v < 2 ^ width) :
    inverseRank u v ≤ 4 * width + 1 := by
  have hsu := Nat.size_le.mpr hu
  have hsv := Nat.size_le.mpr hv
  unfold inverseRank
  split <;> omega

theorem inverseSubtract_size (u v : Nat) :
    (inverseSubtract u v).1.size + (inverseSubtract u v).2.size ≤ u.size + v.size := by
  have hu := Nat.size_le_size (Nat.sub_le u v)
  have hv := Nat.size_le_size (Nat.sub_le v u)
  unfold inverseSubtract
  split <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem inverseSubtract_even {u v : Nat} (hu : u % 2 = 1) (hv : v % 2 = 1) :
    ¬ ((inverseSubtract u v).1 % 2 = 1 ∧ (inverseSubtract u v).2 % 2 = 1) := by
  unfold inverseSubtract
  split <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem size_mul_pow_two {a : Nat} (ha : a ≠ 0) (k : Nat) :
    (a * 2 ^ k).size = a.size + k := by
  simpa only [Nat.shiftLeft_eq] using Nat.size_shiftLeft ha k

/-- Any complete odd-normalization followed by the source subtraction strictly
reduces the rank, including the equal-input case producing a zero operand. -/
theorem inverseRank_normalize_subtract (a b ku kv : Nat)
    (ha : a % 2 = 1) (hb : b % 2 = 1) :
    inverseRank (inverseSubtract a b).1 (inverseSubtract a b).2 <
      inverseRank (a * 2 ^ ku) (b * 2 ^ kv) := by
  have hsz := inverseSubtract_size a b
  have heven := inverseSubtract_even ha hb
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  unfold inverseRank
  rw [if_neg heven, size_mul_pow_two ha0, size_mul_pow_two hb0]
  by_cases hk : ku = 0 ∧ kv = 0
  · obtain ⟨rfl, rfl⟩ := hk
    simp only [Nat.pow_zero, Nat.mul_one, ha, hb, and_self, ↓reduceIte]
    omega
  · split <;> omega

theorem half_size_lt {n : Nat} (hn : 0 < n) : (n / 2).size < n.size := by
  have hpos := Nat.size_pos.mpr hn
  have hnlt := Nat.lt_size_self n
  have hpow : 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
    conv_lhs => rw [show n.size = (n.size - 1) + 1 by omega]
    rw [Nat.pow_succ, Nat.mul_comm]
  have hhalf : n / 2 < 2 ^ (n.size - 1) := by
    rw [hpow] at hnlt
    omega
  have := Nat.size_le.mpr hhalf
  omega

theorem half256_size_lt (a : Limbs256) (h : 0 < a.toNat) :
    (half256 a).toNat.size < a.toNat.size := by
  rw [half256_toNat]
  exact half_size_lt h

theorem inverseRank_256_le (u v : Limbs256) : inverseRank u.toNat v.toNat ≤ 1025 :=
  inverseRank_bound u.toNat_lt v.toNat_lt

theorem inverseRank_384_le {u v : Nat} (hu : u < 2 ^ 384) (hv : v < 2 ^ 384) :
    inverseRank u v ≤ 1537 := inverseRank_bound hu hv

/-- Tight odd-part rank `(oddPart u).size + (oddPart v).size` for R11's `513` and `769` bounds. -/
def oddPart : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then oddPart ((n + 1) / 2) else n + 1

theorem oddPart_zero : oddPart 0 = 0 := by
  rw [oddPart]

theorem oddPart_succ (n : Nat) :
    oddPart (n + 1) = if (n + 1) % 2 = 0 then oddPart ((n + 1) / 2) else n + 1 := by
  rw [oddPart]

theorem oddPart_le : ∀ n : Nat, oddPart n ≤ n
  | 0 => by rw [oddPart_zero]
  | n + 1 => by
    rw [oddPart_succ]
    by_cases h : (n + 1) % 2 = 0
    · rw [if_pos h]
      exact (oddPart_le ((n + 1) / 2)).trans (by omega)
    · rw [if_neg h]

theorem oddPart_of_odd {a : Nat} (ha : a % 2 = 1) : oddPart a = a := by
  cases a with
  | zero => simp at ha
  | succ m =>
    rw [oddPart_succ, if_neg (by omega)]

theorem oddPart_mul_two (x : Nat) : oddPart (x * 2) = oddPart x := by
  cases x with
  | zero => simp [oddPart_zero]
  | succ m =>
    have h1 : (m + 1) * 2 = ((m + 1) * 2 - 1) + 1 := by omega
    rw [h1, oddPart_succ]
    have hev : (((m + 1) * 2 - 1) + 1) % 2 = 0 := by omega
    rw [if_pos hev]
    have hdiv : (((m + 1) * 2 - 1) + 1) / 2 = m + 1 := by omega
    rw [hdiv]

theorem oddPart_mul_pow_two (a : Nat) : ∀ k : Nat, oddPart (a * 2 ^ k) = oddPart a
  | 0 => by simp
  | k + 1 => by
    rw [Nat.pow_succ, ← Nat.mul_assoc, oddPart_mul_two, oddPart_mul_pow_two a k]

theorem oddPart_even_pos {x : Nat} (hpos : 0 < x) (hev : x % 2 = 0) : oddPart x ≤ x / 2 := by
  cases x with
  | zero => omega
  | succ m =>
    rw [oddPart_succ, if_pos hev]
    exact oddPart_le _

def tightInverseRank (u v : Nat) : Nat :=
  (oddPart u).size + (oddPart v).size

theorem tightInverseRank_bound {u v width : Nat}
    (hu : u < 2 ^ width) (hv : v < 2 ^ width) :
    tightInverseRank u v ≤ 2 * width := by
  have hsu := Nat.size_le.mpr (Nat.lt_of_le_of_lt (oddPart_le u) hu)
  have hsv := Nat.size_le.mpr (Nat.lt_of_le_of_lt (oddPart_le v) hv)
  unfold tightInverseRank
  omega

theorem tightInverseRank_normalize_subtract (a b ku kv : Nat)
    (ha : a % 2 = 1) (hb : b % 2 = 1) :
    tightInverseRank (inverseSubtract a b).1 (inverseSubtract a b).2 <
      tightInverseRank (a * 2 ^ ku) (b * 2 ^ kv) := by
  unfold tightInverseRank
  rw [oddPart_mul_pow_two a ku, oddPart_mul_pow_two b kv, oddPart_of_odd ha, oddPart_of_odd hb]
  unfold inverseSubtract
  by_cases hle : b ≤ a
  · rw [if_pos hle]
    dsimp only
    rw [oddPart_of_odd hb]
    by_cases heq : a = b
    · subst heq
      have ha0 : 0 < a := by omega
      have hpos := Nat.size_pos.mpr ha0
      simp [Nat.sub_self, oddPart_zero]
      omega
    · have hpos : 0 < a - b := by omega
      have hev : (a - b) % 2 = 0 := by omega
      have hop := oddPart_even_pos hpos hev
      have hdiv : (a - b) / 2 ≤ a / 2 := Nat.div_le_div_right (Nat.sub_le a b)
      have hsz1 := Nat.size_le_size (hop.trans hdiv)
      have hsz2 := half_size_lt (show 0 < a by omega)
      omega
  · rw [if_neg hle]
    dsimp only
    rw [oddPart_of_odd ha]
    have hpos : 0 < b - a := by omega
    have hev : (b - a) % 2 = 0 := by omega
    have hop := oddPart_even_pos hpos hev
    have hdiv : (b - a) / 2 ≤ b / 2 := Nat.div_le_div_right (Nat.sub_le b a)
    have hsz1 := Nat.size_le_size (hop.trans hdiv)
    have hsz2 := half_size_lt (show 0 < b by omega)
    omega

theorem tightInverseRank_256_le (u v : Limbs256) : tightInverseRank u.toNat v.toNat ≤ 513 :=
  (tightInverseRank_bound u.toNat_lt v.toNat_lt).trans (by decide)

theorem tightInverseRank_384_le {u v : Nat} (hu : u < 2 ^ 384) (hv : v < 2 ^ 384) :
    tightInverseRank u v ≤ 769 :=
  (tightInverseRank_bound hu hv).trans (by decide)
end InitECandidate.Solver.Wave8GuestInv.Arith
