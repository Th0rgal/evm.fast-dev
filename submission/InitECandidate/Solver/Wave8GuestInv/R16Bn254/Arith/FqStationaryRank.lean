import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqStationaryScalar

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
namespace InitECandidate.Solver.Wave8GuestInv.Arith

/-- Phase 2 permits degree descent or residue cancellation, phase 1 permits
quotient-slot cleanup, and phase 0 is reserved for the stationary case.
The degree argument is the current nonnegative active degree, not its rank+1. -/
def divisionStationaryPhase (top slot : Nat) : Nat :=
  if top % fqModulus.toNat = 0 then (if slot = 0 then 0 else 1) else 2

def divisionStationaryRank (degree top slot : Nat) : Nat :=
  degree + divisionStationaryPhase top slot

theorem divisionStationaryPhase_le (top slot : Nat) : divisionStationaryPhase top slot ≤ 2 := by
  unfold divisionStationaryPhase
  split_ifs <;> omega

theorem divisionStationaryRank_le14 (degree top slot : Nat) (hd : degree < 13) :
    divisionStationaryRank degree top slot ≤ 14 := by
  have hp := divisionStationaryPhase_le top slot
  unfold divisionStationaryRank
  omega

/-- A phase-2 step can lower the degree and reset to any phase. -/
theorem divisionStationaryRank_degree_drop (d next top slot newTop newSlot : Nat)
    (ht : top % fqModulus.toNat ≠ 0) (hd : next < d) :
    divisionStationaryRank next newTop newSlot < divisionStationaryRank d top slot := by
  have hp := divisionStationaryPhase_le newTop newSlot
  simp only [divisionStationaryRank,divisionStationaryPhase,if_neg ht]
  unfold divisionStationaryPhase at hp
  omega

/-- A noncanonical top need not drop degree: becoming a modulus multiple
already spends a rank unit, regardless of the quotient slot's new value. -/
theorem divisionStationaryRank_residue_drop (d top slot newTop newSlot : Nat)
    (ht : top % fqModulus.toNat ≠ 0) (hn : newTop % fqModulus.toNat = 0) :
    divisionStationaryRank d newTop newSlot < divisionStationaryRank d top slot := by
  simp only [divisionStationaryRank,divisionStationaryPhase,if_pos hn,if_neg ht]
  split <;> omega

theorem divisionStationaryRank_cleanup_drop (d top slot : Nat)
    (ht : top % fqModulus.toNat = 0) (hs : slot ≠ 0) :
    divisionStationaryRank d top 0 < divisionStationaryRank d top slot := by
  simp [divisionStationaryRank,divisionStationaryPhase,ht,hs]

theorem divisionStationaryPhase_zero_iff (top slot : Nat) :
    divisionStationaryPhase top slot = 0 ↔ top % fqModulus.toNat = 0 ∧ slot = 0 := by
  unfold divisionStationaryPhase
  by_cases ht : top % fqModulus.toNat = 0 <;> by_cases hs : slot = 0 <;> simp [ht,hs]

end InitECandidate.Solver.Wave8GuestInv.Arith
