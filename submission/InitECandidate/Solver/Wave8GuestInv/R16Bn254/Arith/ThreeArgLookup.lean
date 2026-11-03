import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256CallFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem arith_three_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second third : MlS) (ps1 ps2 ps3 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 v3 : ValueHOL width)
    (different : first ≠ second) (diff13 : first ≠ third) (diff23 : second ≠ third)
    (hshape1 : shapeEqHOL ps1 (shapeOfHOLExact v1) = true)
    (hshape2 : shapeEqHOL ps2 (shapeOfHOLExact v2) = true)
    (hshape3 : shapeEqHOL ps3 (shapeOfHOLExact v3) = true)
    (lookup : code name = some ([(first, ps1), (second, ps2), (third, ps3)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2, v3] =
      some (body, ((HolFiniteMapExact.empty.update (first, v1)).update (second, v2)).update (third, v3), rs) := by
  have raw : lookupCodeHOLExact code name [v1, v2, v3] =
      some (body, (fun key => if key = third then some v3 else if key = second then some v2 else if key = first then some v1 else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hshape1, hshape2, hshape3, different, diff13, diff23]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases three : key = third
    · subst three
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have backThree : third ≠ key := Ne.symm three
      by_cases two : key = second
      · subst two
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, diff23, Ne.symm diff23]
      · have backTwo : second ≠ key := Ne.symm two
        by_cases one : key = first
        · subst one
          simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty,
            different, Ne.symm different, diff13, Ne.symm diff13]
        · have backOne : first ≠ key := Ne.symm one
          simp [one, two, three, backOne, backTwo, backThree,
            HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

end InitECandidate.Solver.Wave8GuestInv.Arith
