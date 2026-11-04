import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryWord
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqConvolution

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv

/-- Four machine limbs packed exactly as in the final fq_mul declaration. -/
def montPackLimbs (d : Fin 8 → BitVec 64) : Limbs256 :=
  ⟨d 0 ||| (d 1 <<< (32 : Nat)), d 2 ||| (d 3 <<< (32 : Nat)),
   d 4 ||| (d 5 <<< (32 : Nat)), d 6 ||| (d 7 <<< (32 : Nat))⟩

theorem montPackLimbs_toNat (d : Fin 8 → BitVec 64)
    (hd : ∀ i, (d i).toNat < 2 ^ 32) :
    (montPackLimbs d).toNat = montRadix8 (fun i => (d i).toNat) := by
  simp only [montPackLimbs, Limbs256.toNat]
  rw [montPack32_toNat _ _ (hd 0) (hd 1),
      montPack32_toNat _ _ (hd 2) (hd 3),
      montPack32_toNat _ _ (hd 4) (hd 5),
      montPack32_toNat _ _ (hd 6) (hd 7)]
  dsimp only [montRadix8]
  omega

/-- The global raw-value bound also bounds its last carry digit. -/
theorem montFinalDigit_lt (d : Fin 8 → Nat)
    (hraw : montRadix8 d < 2 ^ 256) : d 7 < 2 ^ 32 := by
  unfold montRadix8 at hraw
  omega

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
