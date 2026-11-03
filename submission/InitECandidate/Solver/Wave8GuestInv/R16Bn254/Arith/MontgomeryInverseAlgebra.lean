import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryReduction

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.Arith

theorem fqRadix_coprime : Nat.gcd fqModulus.toNat (2 ^ 256) = 1 := by decide

/-- The adjustment by R^3 converts an ordinary inverse into a Montgomery inverse.
The premise explicitly requires the multiplication correspondence still to be
established for the source program. -/
theorem montInverse_adjust (p R a x adjustment result : Nat)
    (hcop : Nat.gcd p R = 1)
    (hinv : Nat.ModEq p (a*x) 1)
    (hadj : Nat.ModEq p adjustment (R*R*R))
    (hmul : Nat.ModEq p (R*result) (x*adjustment)) :
    Nat.ModEq p (a*result) (R*R) := by
  apply Nat.ModEq.cancel_left_of_coprime hcop
  have h1 : Nat.ModEq p (R*(a*result)) ((a*x)*adjustment) := by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul.mul_left a
  have h2 : Nat.ModEq p ((a*x)*adjustment) adjustment := by
    simpa only [Nat.one_mul] using hinv.mul_right adjustment
  exact h1.trans (h2.trans (by simpa only [Nat.mul_assoc] using hadj))

/-- Two certified Montgomery multiplications with a Montgomery inverse cancel
one leading coefficient, the algebraic step needed by polynomial division. -/
theorem montInverse_cancel (p R lead divisor inverse quotient product : Nat)
    (hcop : Nat.gcd p R = 1)
    (hinv : Nat.ModEq p (divisor*inverse) (R*R))
    (hquot : Nat.ModEq p (R*quotient) (lead*inverse))
    (hprod : Nat.ModEq p (R*product) (quotient*divisor)) :
    Nat.ModEq p product lead := by
  have h1 : Nat.ModEq p (R*(R*product)) ((R*quotient)*divisor) := by
    simpa only [Nat.mul_assoc] using hprod.mul_left R
  have h2 : Nat.ModEq p ((R*quotient)*divisor) (lead*(divisor*inverse)) := by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hquot.mul_right divisor
  have h3 : Nat.ModEq p (lead*(divisor*inverse)) (R*(R*lead)) := by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hinv.mul_left lead
  exact Nat.ModEq.cancel_left_of_coprime hcop
    (Nat.ModEq.cancel_left_of_coprime hcop (h1.trans (h2.trans h3)))

end InitECandidate.Solver.Wave8GuestInv.Arith
