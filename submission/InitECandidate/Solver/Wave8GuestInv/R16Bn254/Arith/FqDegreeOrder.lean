import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeCorrectCalls

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm

private theorem signed_less_eq (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

def polynomialDegreeRank (w : BitVec 64) : Nat := (w.toInt+1).toNat

theorem degreeIndex_toInt (j : Nat) (hj : j < 13) : (BitVec.ofNat 64 j).toInt = (j : Int) := by
  have he : (BitVec.ofNat 64 j).toInt = ((BitVec.ofNat 64 j).toNat : Int) := by
    simp [BitVec.toInt_eq_msb_cond,BitVec.msb_eq_decide]
    omega
  rw [he]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show j < 2^64 by omega)]

theorem polynomialDegreeValue_range (A : Nat → Limbs256) (w : BitVec 64)
    (h : PolynomialDegreeValue A (.val (.word w))) : -1 ≤ w.toInt ∧ w.toInt ≤ 12 := by
  rcases h with ⟨he,hzero⟩ | ⟨j,hj,he,hne,habove⟩
  · have hw : w = 0-1 := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    subst w
    decide
  · have hw : w = BitVec.ofNat 64 j := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    rw [hw,degreeIndex_toInt j hj]
    omega

theorem polynomialDegreeValue_below (A : Nat → Limbs256) (w : BitVec 64) (d : Nat)
    (h : PolynomialDegreeValue A (.val (.word w))) (hbelow : PolynomialDegreeBelow A d) :
    w.toInt < (d : Int) := by
  rcases h with ⟨he,hzero⟩ | ⟨j,hj,he,hne,habove⟩
  · have hw : w = 0-1 := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    subst w
    change (-1 : Int) < (d : Int)
    omega
  · have hw : w = BitVec.ofNat 64 j := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    have hjd : j < d := by
      by_contra hn
      exact hne (hbelow j hj (by omega))
    rw [hw,degreeIndex_toInt j hj]
    omega

theorem polynomialDegreeValue_nonnegative (A : Nat → Limbs256) (w : BitVec 64)
    (h : PolynomialDegreeValue A (.val (.word w))) (hpos : 0 ≤ w.toInt) :
    ∃ j : Nat, j < 13 ∧ w = BitVec.ofNat 64 j ∧ (A j).toNat ≠ 0 ∧ PolynomialDegreeBelow A (j+1) := by
  rcases h with ⟨he,hzero⟩ | ⟨j,hj,he,hne,habove⟩
  · have hw : w = 0-1 := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    subst w
    change (0 : Int) ≤ -1 at hpos
    omega
  · have hw : w = BitVec.ofNat 64 j := by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    refine ⟨j,hj,hw,hne,?_⟩
    intro k hk hge
    exact habove k (by omega) hk

theorem polynomialDegreeRank_bound (A : Nat → Limbs256) (w : BitVec 64)
    (h : PolynomialDegreeValue A (.val (.word w))) : polynomialDegreeRank w ≤ 13 := by
  have hr := polynomialDegreeValue_range A w h
  unfold polynomialDegreeRank
  omega

theorem polynomialDegreeRank_lt (A : Nat → Limbs256) (before after : BitVec 64)
    (hafter : PolynomialDegreeValue A (.val (.word after))) (hdecrease : after.toInt < before.toInt) :
    polynomialDegreeRank after < polynomialDegreeRank before := by
  have hr := polynomialDegreeValue_range A after hafter
  unfold polynomialDegreeRank
  omega

/-- The actual signed guard gives ordinary, in-range subtraction indices. -/
theorem polynomialDegree_guard_indices (A B : Nat → Limbs256) (before divisor : BitVec 64)
    (ha : PolynomialDegreeValue A (.val (.word before)))
    (hb : PolynomialDegreeValue B (.val (.word divisor)))
    (hpositive : 0 < divisor.toInt)
    (hguard : wordCmpHOL .notLess before divisor = true) :
    ∃ d0 d1 : Nat, d0 < 13 ∧ d1 < 13 ∧ 0 < d1 ∧ d1 ≤ d0 ∧
      before = BitVec.ofNat 64 d0 ∧ divisor = BitVec.ofNat 64 d1 ∧
      before - divisor = BitVec.ofNat 64 (d0-d1) ∧ PolynomialDegreeBelow A (d0+1) := by
  have hge : divisor.toInt ≤ before.toInt := by
    have hn : before.slt divisor ≠ true := by
      simpa only [wordCmpHOL, signed_less_eq, Bool.not_eq_true', Bool.eq_false_iff] using hguard
    exact Int.le_of_not_gt (fun hh => hn (BitVec.slt_iff_toInt_lt.mpr hh))
  obtain ⟨d0,h0,he0,hn0,hd0⟩ := polynomialDegreeValue_nonnegative A before ha (by omega)
  obtain ⟨d1,h1,he1,hn1,hd1⟩ := polynomialDegreeValue_nonnegative B divisor hb (by omega)
  have hi0 := degreeIndex_toInt d0 h0
  have hi1 := degreeIndex_toInt d1 h1
  have hle : d1 ≤ d0 := by rw [he0,he1,hi0,hi1] at hge; omega
  refine ⟨d0,d1,h0,h1,?_,hle,he0,he1,?_,hd0⟩
  · rw [he1,hi1] at hpositive; omega
  · rw [he0,he1,BitVec.ofNat_sub_ofNat_of_le d0 d1 (by omega) hle]

/-- Any certified lower degree makes the machine signed comparison true
and strictly decreases the bounded natural rank, including the sentinel. -/
theorem polynomialDegree_signed_progress (C : Nat → Limbs256) (after : BitVec 64)
    (d : Nat) (hd : d < 13) (hafter : PolynomialDegreeValue C (.val (.word after)))
    (hbelow : PolynomialDegreeBelow C d) :
    wordCmpHOL .less after (BitVec.ofNat 64 d) = true ∧
      polynomialDegreeRank after < polynomialDegreeRank (BitVec.ofNat 64 d) := by
  have hlt : after.toInt < (BitVec.ofNat 64 d).toInt := by
    rw [degreeIndex_toInt d hd]
    exact polynomialDegreeValue_below C after d hafter hbelow
  exact ⟨by simpa only [wordCmpHOL, signed_less_eq, BitVec.slt_iff_toInt_lt] using hlt,
    polynomialDegreeRank_lt C _ after hafter hlt⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
