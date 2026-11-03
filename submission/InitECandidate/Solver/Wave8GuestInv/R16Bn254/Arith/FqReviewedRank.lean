import InitECandidate.Solver.Wave8GuestInv.Expressions

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
namespace InitECandidate.Solver.Wave8GuestInv.Arith

/-- Round-5 review b3963b8f8 phase, parameterized by the field modulus so
its arithmetic can be checked without importing the Montgomery proof cone. -/
def reviewedDivisionPhase (p top slot : Nat) : Nat :=
  if top < p ∨ top % p ≠ 0 then 2 else if slot ≠ 0 then 1 else 0

def reviewedDivisionRank (p d0 d1 linv top slot : Nat) : Nat :=
  (if linv = 0 then 0 else d0-d1) + reviewedDivisionPhase p top slot

theorem reviewedDivisionPhase_le (p top slot : Nat) : reviewedDivisionPhase p top slot ≤ 2 := by
  unfold reviewedDivisionPhase
  split_ifs <;> omega

theorem reviewedDivisionRank_le13 (p d0 d1 linv top slot : Nat)
    (h0 : d0 < 13) (h1 : 1 ≤ d1) : reviewedDivisionRank p d0 d1 linv top slot ≤ 13 := by
  have hp := reviewedDivisionPhase_le p top slot
  unfold reviewedDivisionRank
  split <;> omega

theorem reviewedDivisionPhase_multiple (p top slot : Nat)
    (ht : top ≠ 0) (hm : top % p = 0) :
    reviewedDivisionPhase p top slot = if slot ≠ 0 then 1 else 0 := by
  have hge : ¬ top < p := by
    intro hlt
    exact ht ((Nat.mod_eq_of_lt hlt).symm.trans hm)
  simp [reviewedDivisionPhase,hge,hm]

theorem reviewedDivisionRank_cleanup (p d0 d1 linv top slot : Nat)
    (ht : top ≠ 0) (hm : top % p = 0) (hs : slot ≠ 0) :
    reviewedDivisionRank p d0 d1 linv top 0 < reviewedDivisionRank p d0 d1 linv top slot := by
  simp [reviewedDivisionRank,reviewedDivisionPhase_multiple p top 0 ht hm,
    reviewedDivisionPhase_multiple p top slot ht hm,hs]

theorem reviewedDivisionRank_residue (p d0 d1 linv top slot nextTop nextSlot : Nat)
    (hp : top < p ∨ top % p ≠ 0) (hn : nextTop ≠ 0) (hm : nextTop % p = 0) :
    reviewedDivisionRank p d0 d1 linv nextTop nextSlot <
      reviewedDivisionRank p d0 d1 linv top slot := by
  simp only [reviewedDivisionRank,reviewedDivisionPhase_multiple p nextTop nextSlot hn hm]
  have hphase : reviewedDivisionPhase p top slot = 2 := by simp [reviewedDivisionPhase,hp]
  rw [hphase]
  split_ifs <;> omega

theorem reviewedDivisionRank_degree (p d0 d1 next linv top slot nextTop nextSlot : Nat)
    (hi : linv ≠ 0) (hp : top < p ∨ top % p ≠ 0) (hn : d1 ≤ next) (hd : next < d0) :
    reviewedDivisionRank p next d1 linv nextTop nextSlot <
      reviewedDivisionRank p d0 d1 linv top slot := by
  have hphase : reviewedDivisionPhase p top slot = 2 := by simp [reviewedDivisionPhase,hp]
  have hbound := reviewedDivisionPhase_le p nextTop nextSlot
  simp only [reviewedDivisionRank,if_neg hi,hphase]
  omega

end InitECandidate.Solver.Wave8GuestInv.Arith
