import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.StackBitmapPrefix
open Flapjack Flapjack.StackSemStoreConsts

/-- Extending the bitmap table preserves every successful pattern copy. -/
theorem copyPattern_append {width : Nat} [NeZero width]
    (pattern : BitVec width) (index : Nat) (address offset : BitVec width)
    (bitmaps extra : List (BitVec width)) (domain : BitVec width → Prop)
    [DecidablePred domain] (memory : BitVec width → WordLocW width)
    (result : Nat × BitVec width × (BitVec width → WordLocW width))
    (run : copyWordsForPattern pattern index address offset bitmaps domain memory = some result) :
    copyWordsForPattern pattern index address offset (bitmaps ++ extra) domain memory = some result := by
  induction pattern using (measure (fun p : BitVec width => p.toNat)).wf.induction
      generalizing index address memory result with
  | h pattern ih =>
    by_cases zero : pattern = 0
    · rw [copyWordsForPattern,dif_pos zero] at run
      cases run
    by_cases one : pattern = 1
    · rw [copyWordsForPattern,dif_neg zero,if_pos one] at run ⊢
      exact run
    rw [copyWordsForPattern,dif_neg zero,if_neg one] at run ⊢
    by_cases valid : domain address ∧ index < bitmaps.length
    · rw [dif_pos valid] at run
      have large : domain address ∧ index < (bitmaps ++ extra).length :=
        ⟨valid.1,by simp; omega⟩
      rw [dif_pos large,List.getElem_append_left valid.2]
      apply ih (pattern >>> (1 : Nat)) ?_ (index+1) _ _ result run
      change (pattern >>> (1 : Nat)).toNat < pattern.toNat
      rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_self _ (by decide)
      have nonzero : pattern.toNat ≠ 0 := by
        intro bad
        apply zero
        apply BitVec.eq_of_toNat_eq
        simpa using bad
      omega
    · rw [dif_neg valid] at run
      cases run

/-- Extending the bitmap table preserves every successful complete copy.
This is the primitive refinement needed to compare the initializer's short
fallback bitmap table with the table supplied by native compilation. -/
theorem copyWords_append {width : Nat} [NeZero width]
    (index : Nat) (address offset : BitVec width)
    (bitmaps extra : List (BitVec width)) (domain : BitVec width → Prop)
    [DecidablePred domain] (memory : BitVec width → WordLocW width)
    (result : BitVec width × (BitVec width → WordLocW width))
    (run : copyWordsExact index address offset bitmaps domain memory = some result) :
    copyWordsExact index address offset (bitmaps ++ extra) domain memory = some result := by
  fun_induction copyWordsExact index address offset bitmaps domain memory generalizing result
  case case1 => cases run
  case case2 => cases run
  case case3 i a m bound pattern nextIndex nextAddress nextMemory patternRun sign ih =>
    have low : i < bitmaps.length := by omega
    have lowLarge : i < (bitmaps ++ extra).length := by simp only [List.length_append]; omega
    have patternEq : pattern = bitmaps[i] := by simp only [pattern,getElem!_pos bitmaps i low]
    have same := copyPattern_append pattern (i+1) a offset bitmaps extra domain m _ patternRun
    rw [copyWordsExact,dif_neg (show ¬ (bitmaps ++ extra).length ≤ i by omega)]
    dsimp only
    rw [getElem!_pos (bitmaps ++ extra) i lowLarge,List.getElem_append_left low,← patternEq,same]
    simp only [sign,if_true]
    exact ih result run
  case case4 i a m bound pattern nextIndex nextAddress nextMemory patternRun sign =>
    have low : i < bitmaps.length := by omega
    have lowLarge : i < (bitmaps ++ extra).length := by simp only [List.length_append]; omega
    have patternEq : pattern = bitmaps[i] := by simp only [pattern,getElem!_pos bitmaps i low]
    have same := copyPattern_append pattern (i+1) a offset bitmaps extra domain m _ patternRun
    rw [copyWordsExact,dif_neg (show ¬ (bitmaps ++ extra).length ≤ i by omega)]
    dsimp only
    rw [getElem!_pos (bitmaps ++ extra) i lowLarge,List.getElem_append_left low,← patternEq,same]
    simpa only [sign,Bool.false_eq_true,if_false] using run

set_option pp.fullNames true in
#print axioms copyPattern_append
set_option pp.fullNames true in
#print axioms copyWords_append
end InitECandidate.Solver.Wave8Stage.StackBitmapPrefix
