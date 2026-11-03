import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryDigits
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryReduction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith

/-- The fifteen convolution columns, including all correction products. -/
def fqConvolutionColumns (a b m : Fin 8 → Nat) : Fin 15 → Nat :=
  fun i => match i.val with
    | 0 => fqConvolution0 a b m
    | 1 => fqConvolution1 a b m
    | 2 => fqConvolution2 a b m
    | 3 => fqConvolution3 a b m
    | 4 => fqConvolution4 a b m
    | 5 => fqConvolution5 a b m
    | 6 => fqConvolution6 a b m
    | 7 => fqConvolution7 a b m
    | 8 => fqConvolution8 a b m
    | 9 => fqConvolution9 a b m
    | 10 => fqConvolution10 a b m
    | 11 => fqConvolution11 a b m
    | 12 => fqConvolution12 a b m
    | 13 => fqConvolution13 a b m
    | _ => fqConvolution14 a b m

theorem fqConvolutionColumns_eq (a b m : Fin 8 → Nat) :
    fqWeightedColumns (fqConvolutionColumns a b m) =
      montRadix8 a * montRadix8 b + montRadix8 m * fqModulus.toNat := by
  simpa [fqWeightedColumns, fqConvolutionColumns] using (fqConvolution_eq a b m).symm

/-- Numeric assembly only: the source evaluator must separately supply every
column equation and the correction-digit bounds. One canonical operand suffices. -/
theorem fqColumns_correct (a b : Limbs256) (m : Fin 8 → Nat)
    (carry : Fin 16 → Nat) (digits : Fin 7 → Nat)
    (hb : b.toNat < fqModulus.toNat)
    (hm : ∀ i, m i < 2 ^ 32)
    (hzero : carry 0 = 0)
    (h0 : 4294967296 * carry 1 = carry 0 + fqConvolution0 (limbs256Digits a) (limbs256Digits b) m)
    (h1 : 4294967296 * carry 2 = carry 1 + fqConvolution1 (limbs256Digits a) (limbs256Digits b) m)
    (h2 : 4294967296 * carry 3 = carry 2 + fqConvolution2 (limbs256Digits a) (limbs256Digits b) m)
    (h3 : 4294967296 * carry 4 = carry 3 + fqConvolution3 (limbs256Digits a) (limbs256Digits b) m)
    (h4 : 4294967296 * carry 5 = carry 4 + fqConvolution4 (limbs256Digits a) (limbs256Digits b) m)
    (h5 : 4294967296 * carry 6 = carry 5 + fqConvolution5 (limbs256Digits a) (limbs256Digits b) m)
    (h6 : 4294967296 * carry 7 = carry 6 + fqConvolution6 (limbs256Digits a) (limbs256Digits b) m)
    (h7 : 4294967296 * carry 8 = carry 7 + fqConvolution7 (limbs256Digits a) (limbs256Digits b) m)
    (h8 : digits 0 + 4294967296 * carry 9 = carry 8 + fqConvolution8 (limbs256Digits a) (limbs256Digits b) m)
    (h9 : digits 1 + 4294967296 * carry 10 = carry 9 + fqConvolution9 (limbs256Digits a) (limbs256Digits b) m)
    (h10 : digits 2 + 4294967296 * carry 11 = carry 10 + fqConvolution10 (limbs256Digits a) (limbs256Digits b) m)
    (h11 : digits 3 + 4294967296 * carry 12 = carry 11 + fqConvolution11 (limbs256Digits a) (limbs256Digits b) m)
    (h12 : digits 4 + 4294967296 * carry 13 = carry 12 + fqConvolution12 (limbs256Digits a) (limbs256Digits b) m)
    (h13 : digits 5 + 4294967296 * carry 14 = carry 13 + fqConvolution13 (limbs256Digits a) (limbs256Digits b) m)
    (h14 : digits 6 + 4294967296 * carry 15 = carry 14 + fqConvolution14 (limbs256Digits a) (limbs256Digits b) m)
    : let raw := digits 0 * 1 + digits 1 * 4294967296 + digits 2 * 18446744073709551616 +
        digits 3 * 79228162514264337593543950336 +
        digits 4 * 340282366920938463463374607431768211456 +
        digits 5 * 1461501637330902918203684832716283019655932542976 +
        digits 6 * 6277101735386680763835789423207666416102355444464034512896 +
        carry 15 * 26959946667150639794667015087019630673637144422540572481103610249216
      raw < 2 ^ 256 ∧ montFinalReduce raw fqModulus.toNat < fqModulus.toNat ∧
        Nat.ModEq fqModulus.toNat (2 ^ 256 * montFinalReduce raw fqModulus.toNat)
          (a.toNat * b.toNat) := by
  have ht := fqColumns_telescope
    (fqConvolutionColumns (limbs256Digits a) (limbs256Digits b) m) carry digits
    hzero h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  rw [fqConvolutionColumns_eq, limbs256Digits_value, limbs256Digits_value] at ht
  exact fqMontReduction_correct a.toNat b.toNat (montRadix8 m) _
    (by simpa only [limbs256Digits_value] using
      montRadix8_lt (limbs256Digits a) (limbs256Digits_lt a))
    hb (montRadix8_lt m hm) ht

end InitECandidate.Solver.Wave8GuestInv.Arith
