import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeOrder

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def polynomialRankUpTo (A : Nat → Limbs256) : Nat → Nat
  | 0 => 0
  | n+1 => if (A n).toNat = 0 then polynomialRankUpTo A n else n+1

theorem polynomialRankUpTo_bound (A : Nat → Limbs256) (n : Nat) : polynomialRankUpTo A n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [polynomialRankUpTo]; split <;> omega

theorem polynomialRankUpTo_below (A : Nat → Limbs256) (n d : Nat)
    (hn : n ≤ 13) (hd : PolynomialDegreeBelow A d) : polynomialRankUpTo A n ≤ d := by
  induction n with
  | zero => simp [polynomialRankUpTo]
  | succ n ih =>
      simp only [polynomialRankUpTo]
      split
      · exact ih (by omega)
      · rename_i hne
        have hlt : n < d := by
          by_contra hnot
          exact hne (hd n (by omega) (by omega))
        omega

theorem polynomialRankUpTo_nonzero (A : Nat → Limbs256) (j n : Nat)
    (hj : j < n) (hne : (A j).toNat ≠ 0) : j+1 ≤ polynomialRankUpTo A n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases he : n = j
      · subst n; simp [polynomialRankUpTo,hne]
      · simp only [polynomialRankUpTo]
        split
        · exact ih (by omega)
        · omega

theorem polynomialRankUpTo_congr (A B : Nat → Limbs256) (n : Nat)
    (h : ∀ j, j < n → A j = B j) : polynomialRankUpTo A n = polynomialRankUpTo B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [polynomialRankUpTo,h n (by omega)]
      rw [ih (fun j hj => h j (by omega))]

theorem polynomialRankUpTo_degree (A : Nat → Limbs256) (w : BitVec 64)
    (h : PolynomialDegreeValue A (.val (.word w))) : polynomialRankUpTo A 13 = polynomialDegreeRank w := by
  rcases h with ⟨he,hzero⟩ | ⟨j,hj,he,hne,habove⟩
  · have hw : w = 0-1 := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    have hr := polynomialRankUpTo_below A 13 0 (by decide) (fun j hj _ => hzero j hj)
    have hz : polynomialDegreeRank (0-1) = 0 := by decide
    rw [hw,hz]
    omega
  · have hw : w = BitVec.ofNat 64 j := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    have hup := polynomialRankUpTo_below A 13 (j+1) (by decide) (fun k hk hge => habove k (by omega) hk)
    have hlo := polynomialRankUpTo_nonzero A j 13 hj hne
    have heq : polynomialRankUpTo A 13 = j+1 := by omega
    rw [heq,hw]
    simp [polynomialDegreeRank,degreeIndex_toInt j hj]

def polynomialMemoryWord (memory : BitVec 64 → HolWordLab 64) (address : BitVec 64) : BitVec 64 :=
  match memory address with | .word w => w

def polynomialMemoryCoefficients (memory : BitVec 64 → HolWordLab 64) (base : BitVec 64)
    (j : Nat) : Limbs256 :=
  ⟨polynomialMemoryWord memory (coefficientAddress base j),
   polynomialMemoryWord memory (coefficientAddress base j + 8),
   polynomialMemoryWord memory (coefficientAddress base j + 16),
   polynomialMemoryWord memory (coefficientAddress base j + 24)⟩

theorem polynomialMemoryCoefficients_read (memory : BitVec 64 → HolWordLab 64) (base : BitVec 64)
    (A : Nat → Limbs256) (hm : MemoryPolynomial memory base A) (j : Nat) (hj : j < 13) :
    polynomialMemoryCoefficients memory base j = A j := by
  rcases hm j hj with ⟨h0,h1,h2,h3⟩
  cases hA : A j
  simp_all [polynomialMemoryCoefficients,polynomialMemoryWord]

def polynomialMemoryRank (memory : BitVec 64 → HolWordLab 64) (base : BitVec 64) : Nat :=
  polynomialRankUpTo (polynomialMemoryCoefficients memory base) 13

theorem polynomialMemoryRank_represented (memory : BitVec 64 → HolWordLab 64) (base : BitVec 64)
    (A : Nat → Limbs256) (w : BitVec 64) (hm : MemoryPolynomial memory base A)
    (hd : PolynomialDegreeValue A (.val (.word w))) : polynomialMemoryRank memory base = polynomialDegreeRank w := by
  unfold polynomialMemoryRank
  rw [polynomialRankUpTo_congr _ A 13 (polynomialMemoryCoefficients_read memory base A hm)]
  exact polynomialRankUpTo_degree A w hd

/-- Outer-loop rank reads the current r1 buffer, so it survives restoration
of the scoped d0/d1 locals and follows the source's pointer swap. -/
def polyOuterRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "r1") with
  | some (.val (.word base)) => polynomialMemoryRank s.memory base
  | _ => 0

theorem polyOuterRank_bound {F : Type} (s : PanSemStateFiniteExact 64 F) : polyOuterRank s ≤ 13 := by
  unfold polyOuterRank
  split
  · exact polynomialRankUpTo_bound _ 13
  · omega

theorem polyOuterRank_represented {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (A : Nat → Limbs256) (degree : BitVec 64)
    (hl : s.locals.lookup (ofString "r1") = some (.val (.word base)))
    (hm : MemoryPolynomial s.memory base A) (hd : PolynomialDegreeValue A (.val (.word degree))) :
    polyOuterRank s = polynomialDegreeRank degree := by
  simp only [polyOuterRank,hl]
  exact polynomialMemoryRank_represented s.memory base A degree hm hd

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
