import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInverseSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv

/-- The low-column correction digit used literally by fq_mul. -/
def fqCorrectionDigit (digit : Nat) : Nat := (digit * 3834012553) % 2 ^ 32

theorem fqCorrectionDigit_lt (digit : Nat) : fqCorrectionDigit digit < 2 ^ 32 :=
  Nat.mod_lt _ (by decide)

theorem fqCorrectionDigit_cancels (digit : Nat) :
    (digit + fqCorrectionDigit digit * 3632069959) % 2 ^ 32 = 0 := by
  unfold fqCorrectionDigit
  calc
    (digit + digit * 3834012553 % 2 ^ 32 * 3632069959) % 2 ^ 32 =
        (digit * (3834012553 * 3632069959 + 1)) % 2 ^ 32 := by
      rw [show digit * (3834012553 * 3632069959 + 1) =
        digit + (digit * 3834012553) * 3632069959 by ring]
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    _ = 0 := by
      rw [Nat.mul_mod]
      norm_num

/-- The four summands in the actual low-column carry assignment. -/
def montLowerCarry (low high carry correction primeWord : Nat) : Nat :=
  (low + carry) / 2 ^ 32 + high +
    ((low + carry) % 2 ^ 32 + (correction * primeWord) % 2 ^ 32) / 2 ^ 32 +
    (correction * primeWord) / 2 ^ 32

theorem montLowerCarry_conserve (low high carry correction primeWord : Nat)
    (hc : ((low + carry) % 2 ^ 32 + correction * primeWord) % 2 ^ 32 = 0) :
    2 ^ 32 * montLowerCarry low high carry correction primeWord =
      low + 2 ^ 32 * high + carry + correction * primeWord := by
  unfold montLowerCarry
  omega

theorem montLowerCarry_lt (low high carry correction primeWord : Nat)
    (hl : low ≤ 16 * 2 ^ 32) (hh : high ≤ 16 * 2 ^ 32)
    (hc : carry < 32 * 2 ^ 32) (hm : correction < 2 ^ 32) (hp : primeWord < 2 ^ 32) :
    montLowerCarry low high carry correction primeWord < 32 * 2 ^ 32 := by
  have hprod : correction * primeWord < 2 ^ 64 := by nlinarith
  unfold montLowerCarry
  omega

theorem fqLowerCarry_conserve (low high carry : Nat) :
    2 ^ 32 * montLowerCarry low high carry (fqCorrectionDigit ((low + carry) % 2 ^ 32)) 3632069959 =
      low + 2 ^ 32 * high + carry + fqCorrectionDigit ((low + carry) % 2 ^ 32) * 3632069959 :=
  montLowerCarry_conserve _ _ _ _ _ (fqCorrectionDigit_cancels _)

def montUpperCarry (low high carry : Nat) : Nat := (low + carry) / 2 ^ 32 + high

theorem montUpperCarry_conserve (low high carry : Nat) :
    (low + carry) % 2 ^ 32 + 2 ^ 32 * montUpperCarry low high carry =
      low + 2 ^ 32 * high + carry := by
  unfold montUpperCarry
  omega

theorem montUpperCarry_lt (low high carry : Nat)
    (hl : low ≤ 16 * 2 ^ 32) (hh : high ≤ 16 * 2 ^ 32) (hc : carry < 32 * 2 ^ 32) :
    montUpperCarry low high carry < 32 * 2 ^ 32 := by
  unfold montUpperCarry
  omega

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
