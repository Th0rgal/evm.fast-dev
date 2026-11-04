import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryWord
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryColumn

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv

def fqCorrectionWord (digit : BitVec 64) : BitVec 64 := montLow32 (digit * 3834012553#64)

theorem fqCorrectionWord_toNat (digit : BitVec 64) (hd : digit.toNat < 2 ^ 32) :
    (fqCorrectionWord digit).toNat = fqCorrectionDigit digit.toNat := by
  rw [fqCorrectionWord, montLow32_toNat, montDigit_mul_toNat digit 3834012553#64 hd (by decide)]
  rfl

def montLowerCarryWord (low high carry : BitVec 64) : BitVec 64 :=
  let col := low + carry
  let digit := montLow32 col
  let correction := fqCorrectionWord digit
  let product := correction * 3632069959#64
  let col2 := digit + montLow32 product
  montHigh32 col + (high + (montHigh32 col2 + montHigh32 product))

/-- A bounded four-word sum, proved independently to keep kernel reduction
of the nested Montgomery expressions out of the arithmetic certificate. -/
theorem montCarryFourSum_toNat (a b c d : BitVec 64)
    (ha : a.toNat < 48) (hb : b.toNat ≤ 16 * 2 ^ 32)
    (hc : c.toNat < 2) (hd : d.toNat < 2 ^ 32) :
    (a + (b + (c+d))).toNat = a.toNat + b.toNat + c.toNat + d.toNat := by
  have hcd : (c+d).toNat = c.toNat + d.toNat :=
    montAccumulator_add_toNat _ _ (by omega) (by omega)
  have hbcd : (b+(c+d)).toNat = b.toNat + (c+d).toNat :=
    montAccumulator_add_toNat _ _ hb (by rw [hcd]; omega)
  have habcd : (a+(b+(c+d))).toNat = a.toNat + (b+(c+d)).toNat :=
    montAccumulator_add_toNat _ _ (by omega) (by rw [hbcd, hcd]; omega)
  rw [habcd, hbcd, hcd]
  omega

theorem montLowerCarryWord_toNat (low high carry : BitVec 64)
    (hl : low.toNat ≤ 16 * 2 ^ 32) (hh : high.toNat ≤ 16 * 2 ^ 32)
    (hc : carry.toNat < 32 * 2 ^ 32) :
    (montLowerCarryWord low high carry).toNat =
      montLowerCarry low.toNat high.toNat carry.toNat
        (fqCorrectionDigit ((low.toNat + carry.toNat) % 2 ^ 32)) 3632069959 := by
  let col := low + carry
  let digit := montLow32 col
  let correction := fqCorrectionWord digit
  let product := correction * 3632069959#64
  let col2 := digit + montLow32 product
  have hcol : col.toNat = low.toNat + carry.toNat := montAccumulator_add_toNat _ _ hl hc
  have hdval : digit.toNat = (low.toNat + carry.toNat) % 2 ^ 32 := by
    rw [montLow32_toNat, hcol]
  have hd : digit.toNat < 2 ^ 32 := montLow32_lt col
  have hm : correction.toNat < 2 ^ 32 := montLow32_lt _
  have hmval : correction.toNat = fqCorrectionDigit ((low.toNat + carry.toNat) % 2 ^ 32) := by
    rw [fqCorrectionWord_toNat _ hd, montLow32_toNat, hcol]
  have hprod : product.toNat = correction.toNat * 3632069959 := by
    exact montDigit_mul_toNat correction 3632069959#64 hm (by decide)
  have hpLow := montLow32_lt product
  have hcol2 : col2.toNat = digit.toNat + (montLow32 product).toNat :=
    montAccumulator_add_toNat _ _ (by omega) (by omega)
  have hhi := montHigh32_lt product
  have hcHi : (montHigh32 col).toNat < 48 := by rw [montHigh32_toNat, hcol]; omega
  have hc2Hi : (montHigh32 col2).toNat < 2 := by rw [montHigh32_toNat, hcol2]; omega
  have hsum : (montLowerCarryWord low high carry).toNat =
      (montHigh32 col).toNat + high.toNat + (montHigh32 col2).toNat + (montHigh32 product).toNat := by
    change (montHigh32 col + (high + (montHigh32 col2 + montHigh32 product))).toNat = _
    exact montCarryFourSum_toNat _ _ _ _ hcHi hh hc2Hi hhi
  rw [hsum]
  simp only [montHigh32_toNat, hcol, hcol2, montLow32_toNat, hprod, hmval, hdval]
  change (low.toNat + carry.toNat) / 2 ^ 32 + high.toNat +
    (((low.toNat + carry.toNat) % 2 ^ 32 +
      (fqCorrectionDigit ((low.toNat + carry.toNat) % 2 ^ 32) * 3632069959) % 2 ^ 32) / 2 ^ 32) +
    (fqCorrectionDigit ((low.toNat + carry.toNat) % 2 ^ 32) * 3632069959) / 2 ^ 32 = _
  rfl

theorem montLowerCarryWord_conserve (low high carry : BitVec 64)
    (hl : low.toNat ≤ 16 * 2 ^ 32) (hh : high.toNat ≤ 16 * 2 ^ 32)
    (hc : carry.toNat < 32 * 2 ^ 32) :
    2 ^ 32 * (montLowerCarryWord low high carry).toNat =
      low.toNat + 2 ^ 32 * high.toNat + carry.toNat +
        fqCorrectionDigit ((low.toNat + carry.toNat) % 2 ^ 32) * 3632069959 := by
  rw [montLowerCarryWord_toNat low high carry hl hh hc]
  exact fqLowerCarry_conserve _ _ _

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
