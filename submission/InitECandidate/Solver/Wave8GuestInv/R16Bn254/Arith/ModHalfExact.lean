import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModularArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
attribute [local irreducible] wordAddCarryHOL addCarry256

private theorem modhalf_exact_two_arg_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    (different : first ≠ second)
    (hshape1 : shapeEqHOL ps1 (shapeOfHOLExact v1) = true)
    (hshape2 : shapeEqHOL ps2 (shapeOfHOLExact v2) = true)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] =
      some (body, (HolFiniteMapExact.empty.update (first, v1)).update (second, v2), rs) := by
  have raw : lookupCodeHOLExact code name [v1, v2] =
      some (body, (fun key => if key = second then some v2 else if key = first then some v1 else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hshape1, hshape2, different]
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
    by_cases two : key = second
    · subst two
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have backTwo : second ≠ key := Ne.symm two
      by_cases one : key = first
      · subst one
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, different, Ne.symm different]
      · have backOne : first ≠ key := Ne.symm one
        simp [one, two, backOne, backTwo, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

theorem modHalfOdd_exact {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : Limbs256) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "x") = some a.toValue)
    (hb : s.locals.lookup (ofString "m") = some b.toValue) :
    (evaluateHOLFiniteState s modHalfOddBody).1 = some .timeOut ∨
      (evaluateHOLFiniteState s modHalfOddBody).1 = some (.returned (carryHalf256 (addCarry256 a b).1 (addCarry256 a b).2).toValue) := by
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "x"), .var .local (ofString "m")] = some [a.toValue, b.toValue] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
  let locals := (HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update (ofString "b", b.toValue)
  have hlookup : lookupCodeHOLFinite s.code.lookup (ofString "u256_add_carry") [a.toValue, b.toValue] =
      some (arithSourceBody Guest.Software.guestFn_u256_add_carry, locals,
        .comb [.one, .one, .one, .one, .one]) := by
    apply modhalf_exact_two_arg_lookup s.code.lookup (ofString "u256_add_carry")
      (ofString "a") (ofString "b") arithU256Shape arithU256Shape
      (.comb [.one, .one, .one, .one, .one])
      (arithSourceBody Guest.Software.guestFn_u256_add_carry) a.toValue b.toValue (by decide)
    · simp [arithU256Shape, Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [arithU256Shape, Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · rw [hc]
      exact arith_lookup_u256_add_carry
  unfold modHalfOddBody
  rw [evaluateHOLFiniteState_decCall_total, hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  by_cases hz : s.clock = 0
  · left
    simp [hz]
  · rw [if_neg hz]
    obtain ⟨post, hrun, _⟩ := eval_u256_add_carry_body (callEntryStateHOLFinite s locals) a b
      (by simp [locals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "b" ≠ ofString "a" by decide])
      (by simp [locals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    have hclock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s locals)
      (arithSourceBody Guest.Software.guestFn_u256_add_carry)
    rw [hrun] at hclock
    have hfix : fixClockHOLFinite (callEntryStateHOLFinite s locals)
        (some (PanSemResultExact.returned (addCarry256Value a b)), post) =
        (some (PanSemResultExact.returned (addCarry256Value a b)), post) := by
      simp [fixClockHOLFinite, Nat.not_lt.mpr hclock]
    rw [hrun, hfix]
    dsimp only
    have hshape : shapeEqHOL (shapeOfHOLExact (addCarry256Value a b))
        (.comb [.one, .one, .one, .one, .one]) = true := by
      simp [addCarry256Value, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    rw [hshape]
    right
    have he := inverseCarryHalfExpr_eval
      (setVarHOLFinite (ofString "s") (addCarry256Value a b) {post with locals := s.locals})
      (ofString "s") a b (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    dsimp only [arithEval] at he
    simp [evaluateHOLFiniteState_return, he, Limbs256.toValue, shapeOfHOLExact,
      sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]

theorem modHalf_exact {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : Limbs256) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "x") = some a.toValue)
    (hb : s.locals.lookup (ofString "m") = some b.toValue) :
    (evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_mod_half)).1 = some .timeOut ∨
      (evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_mod_half)).1 = some (.returned (modHalf256 a b).toValue) := by
  have hg := inverseEvenExpr_eval s (ofString "x") a ha
  have hh := inverseHalfExpr_eval s (ofString "x") a ha
  dsimp only [arithEval] at hg hh
  rw [modHalf_source_eq, evaluateHOLFiniteState_seq_line780]
  by_cases he : a.toNat % 2 = 0
  · have hfirst : evaluateHOLFiniteState s
        (.ite (inverseEvenExpr (ofString "x")) (.return (inverseHalfExpr (ofString "x"))) .skip) =
        (some (.returned (half256 a).toValue), emptyLocalsHOLFinite s) := by
      simp [evaluateHOLFiniteState_ite, hg, he, evaluateHOLFiniteState_return, hh, Limbs256.toValue, shapeOfHOLExact,
        sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
    rw [hfirst]
    exact Or.inr (by simp [modHalf256, he])
  · have hfirst : evaluateHOLFiniteState s
        (.ite (inverseEvenExpr (ofString "x")) (.return (inverseHalfExpr (ofString "x"))) .skip) =
        (none, s) := by
      simp [evaluateHOLFiniteState_ite, hg, he, evaluateHOLFiniteState_skip]
    rw [hfirst]
    simpa only [modHalf256, if_neg he] using modHalfOdd_exact s a b hc ha hb


end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
