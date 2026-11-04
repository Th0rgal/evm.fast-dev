import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqConvolution
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryWord

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv

def limbs256Digits (a : Limbs256) : Fin 8 → Nat := fun i =>
  if i.val = 0 then (montLow32 a.l0).toNat else
  if i.val = 1 then (montHigh32 a.l0).toNat else
  if i.val = 2 then (montLow32 a.l1).toNat else
  if i.val = 3 then (montHigh32 a.l1).toNat else
  if i.val = 4 then (montLow32 a.l2).toNat else
  if i.val = 5 then (montHigh32 a.l2).toNat else
  if i.val = 6 then (montLow32 a.l3).toNat else (montHigh32 a.l3).toNat

theorem limbs256Digits_lt (a : Limbs256) (i : Fin 8) : limbs256Digits a i < 2 ^ 32 := by
  fin_cases i
  all_goals first | exact montLow32_lt _ | exact montHigh32_lt _

theorem limbs256Digits_value (a : Limbs256) : montRadix8 (limbs256Digits a) = a.toNat := by
  have h0 := montWord_split a.l0
  have h1 := montWord_split a.l1
  have h2 := montWord_split a.l2
  have h3 := montWord_split a.l3
  dsimp [montRadix8, limbs256Digits, Limbs256.toNat]
  omega

theorem montRadix8_lt (a : Fin 8 → Nat) (ha : ∀ i, a i < 2 ^ 32) :
    montRadix8 a < 2 ^ 256 := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have h4 := ha 4
  have h5 := ha 5
  have h6 := ha 6
  have h7 := ha 7
  unfold montRadix8
  omega

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
