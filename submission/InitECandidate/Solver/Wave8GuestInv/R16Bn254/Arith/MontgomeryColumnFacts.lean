import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryProductList
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryCarry
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryUpper

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv

/-- Numeric contract of a complete bounded product list starting from zero. -/
theorem montAccWords_zero_correct (products : List (BitVec 64 × BitVec 64))
    (hn : products.length ≤ 16)
    (hp : ∀ ab ∈ products, ab.1.toNat < 2 ^ 32 ∧ ab.2.toNat < 2 ^ 32) :
    (montAccWords 0 0 products).1.toNat ≤ 16 * 2 ^ 32 ∧
    (montAccWords 0 0 products).2.toNat ≤ 16 * 2 ^ 32 ∧
    (montAccWords 0 0 products).1.toNat +
      2 ^ 32 * (montAccWords 0 0 products).2.toNat = montProductSum products := by
  have h := montAccWords_correct products 0 0 0 (by simpa using hn) (by decide) (by decide) hp
  have hbound : products.length * (2 ^ 32 - 1) ≤ 16 * 2 ^ 32 :=
    (Nat.mul_le_mul_right _ hn).trans (Nat.mul_le_mul_left 16 (Nat.sub_le _ _))
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.le_trans _ hbound
    simpa only [Nat.zero_add] using h.1
  · apply Nat.le_trans _ hbound
    simpa only [Nat.zero_add] using h.2.1
  · simpa using h.2.2

/-- Product-list conservation plus the actual lower carry word gives the next
column equation. Bounds are retained for chaining all eight lower columns. -/
theorem montLowerProducts_correct (products : List (BitVec 64 × BitVec 64))
    (carry : BitVec 64) (hn : products.length ≤ 16)
    (hp : ∀ ab ∈ products, ab.1.toNat < 2 ^ 32 ∧ ab.2.toNat < 2 ^ 32)
    (hc : carry.toNat < 32 * 2 ^ 32) :
    let low := (montAccWords 0 0 products).1
    let high := (montAccWords 0 0 products).2
    let correction := fqCorrectionWord (montLow32 (low+carry))
    correction.toNat < 2 ^ 32 ∧
      (montLowerCarryWord low high carry).toNat < 32 * 2 ^ 32 ∧
      2 ^ 32 * (montLowerCarryWord low high carry).toNat =
        montProductSum products + carry.toNat + correction.toNat * 3632069959 := by
  let low := (montAccWords 0 0 products).1
  let high := (montAccWords 0 0 products).2
  have hs := montAccWords_zero_correct products hn hp
  have hl : low.toNat ≤ 16 * 2 ^ 32 := hs.1
  have hh : high.toNat ≤ 16 * 2 ^ 32 := hs.2.1
  have hm : (fqCorrectionWord (montLow32 (low+carry))).toNat =
      fqCorrectionDigit ((low.toNat + carry.toNat) % 2 ^ 32) := by
    rw [fqCorrectionWord_toNat _ (montLow32_lt _), montLow32_toNat,
      montAccumulator_add_toNat low carry hl hc]
  refine ⟨montLow32_lt _, ?_, ?_⟩
  · rw [montLowerCarryWord_toNat low high carry hl hh hc]
    exact montLowerCarry_lt _ _ _ _ _ hl hh hc (fqCorrectionDigit_lt _) (by decide)
  · rw [montLowerCarryWord_conserve low high carry hl hh hc, hm]
    exact congrArg (fun x => x + carry.toNat +
      fqCorrectionDigit ((low.toNat + carry.toNat) % 2 ^ 32) * 3632069959) hs.2.2

/-- The upper-column equation emits a bounded digit and propagates a bounded
carry, preserving the exact product sum. -/
theorem montUpperProducts_correct (products : List (BitVec 64 × BitVec 64))
    (carry : BitVec 64) (hn : products.length ≤ 16)
    (hp : ∀ ab ∈ products, ab.1.toNat < 2 ^ 32 ∧ ab.2.toNat < 2 ^ 32)
    (hc : carry.toNat < 32 * 2 ^ 32) :
    let low := (montAccWords 0 0 products).1
    let high := (montAccWords 0 0 products).2
    (montLow32 (low+carry)).toNat < 2 ^ 32 ∧
      (montUpperCarryWord low high carry).toNat < 32 * 2 ^ 32 ∧
      (montLow32 (low+carry)).toNat + 2 ^ 32 * (montUpperCarryWord low high carry).toNat =
        montProductSum products + carry.toNat := by
  let low := (montAccWords 0 0 products).1
  let high := (montAccWords 0 0 products).2
  have hs := montAccWords_zero_correct products hn hp
  have hl : low.toNat ≤ 16 * 2 ^ 32 := hs.1
  have hh : high.toNat ≤ 16 * 2 ^ 32 := hs.2.1
  refine ⟨montLow32_lt _, ?_, ?_⟩
  · rw [montUpperCarryWord_toNat low high carry hl hh hc]
    exact montUpperCarry_lt _ _ _ hl hh hc
  · rw [montUpperCarryWord_conserve low high carry hl hh hc]
    exact congrArg (fun x => x + carry.toNat) hs.2.2

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
