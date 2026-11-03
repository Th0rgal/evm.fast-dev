import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsUnaryCall
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsCarrySemantics

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
attribute [local irreducible] wordAddCarryHOL addCarry384

private theorem bls_two_arg_lookup {width : Nat} [NeZero width]
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

def blsModulus : Limbs384 := ⟨13402431016077863595, 2210141511517208575, 7435674573564081700, 7239337960414712511, 5412103778470702295, 1873798617647539866⟩
def blsModulusExpr : ExpHOL 64 := .rstruct [.const 13402431016077863595, .const 2210141511517208575, .const 7435674573564081700, .const 7239337960414712511, .const 5412103778470702295, .const 1873798617647539866]

def blsCarryHalfExpr (counter : MlS) : ExpHOL 64 :=
  .rstruct [
    .op .or [.shift .lsr (.rfield 0 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 1 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 1 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 2 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 2 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 3 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 3 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 4 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 4 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 5 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 5 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 6 (.var .local counter)) (.const 63)]]

def carryHalf384 (a : Limbs384) (carry : BitVec 64) : Limbs384 :=
  ⟨halfWord256 a.l0 a.l1, halfWord256 a.l1 a.l2, halfWord256 a.l2 a.l3,
    halfWord256 a.l3 a.l4, halfWord256 a.l4 a.l5, halfWord256 a.l5 carry⟩

theorem blsCarryHalfExpr_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a b : Limbs384)
    (hl : s.locals.lookup counter = some (carry384Value (addCarry384 a b))) :
    arithEval s (blsCarryHalfExpr counter) =
      some (carryHalf384 (addCarry384 a b).1 (addCarry384 a b).2).toValue := by
  simp [blsCarryHalfExpr, arithEval, evalHOLExact, evalListHOLExact, hl,
    Limbs384.toValue, carry384Value, wordShiftHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
    carryHalf384, halfWord256, OrOp.or]

def blsModHalfOddBody : ProgHOL 64 :=
  .decCall (ofString "s") blsCarryShape (ofString "bls_fp_add_raw")
    [.var .local (ofString "x"), blsModulusExpr]
    (.return (blsCarryHalfExpr (ofString "s")))

theorem blsModHalf_source_eq : arithSourceBody Guest.Software.guestFn_bls_fp_half_can =
    .seq (.ite (inverseEvenExpr (ofString "x"))
      (.call none (ofString "bls_fp_shr1") [.var .local (ofString "x")]) .skip) blsModHalfOddBody := rfl

theorem blsModHalfOdd_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a : Limbs384) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "x") = some a.toValue) :
    (evaluateHOLFiniteState s blsModHalfOddBody).1 = some .timeOut ∨
      ∃ r : Limbs384, (evaluateHOLFiniteState s blsModHalfOddBody).1 = some (.returned r.toValue) := by
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "x"), blsModulusExpr] = some [a.toValue, blsModulus.toValue] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, blsModulusExpr, blsModulus, Limbs384.toValue]
  let locals := (HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update (ofString "b", blsModulus.toValue)
  have hlookup : lookupCodeHOLFinite s.code.lookup (ofString "bls_fp_add_raw") [a.toValue, blsModulus.toValue] =
      some (arithSourceBody Guest.Software.guestFn_bls_fp_add_raw, locals,
        blsCarryShape) := by
    apply bls_two_arg_lookup s.code.lookup (ofString "bls_fp_add_raw")
      (ofString "a") (ofString "b") blsU384Shape blsU384Shape
      blsCarryShape
      (arithSourceBody Guest.Software.guestFn_bls_fp_add_raw) a.toValue blsModulus.toValue (by decide)
    · simp [blsU384Shape, Limbs384.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [blsU384Shape, Limbs384.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · rw [hc]
      exact arith_lookup_bls_fp_add_raw
  unfold blsModHalfOddBody
  rw [evaluateHOLFiniteState_decCall_total, hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  by_cases hz : s.clock = 0
  · left
    simp [hz]
  · rw [if_neg hz]
    obtain ⟨post, hrun, _⟩ := eval_bls_fp_add_raw_body (callEntryStateHOLFinite s locals) a blsModulus
      (by simp [locals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "b" ≠ ofString "a" by decide])
      (by simp [locals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    have hclock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s locals)
      (arithSourceBody Guest.Software.guestFn_bls_fp_add_raw)
    rw [hrun] at hclock
    have hfix : fixClockHOLFinite (callEntryStateHOLFinite s locals)
        (some (PanSemResultExact.returned (carry384Value (addCarry384 a blsModulus))), post) =
        (some (PanSemResultExact.returned (carry384Value (addCarry384 a blsModulus))), post) := by
      simp [fixClockHOLFinite, Nat.not_lt.mpr hclock]
    rw [hrun, hfix]
    dsimp only
    have hshape : shapeEqHOL (shapeOfHOLExact (carry384Value (addCarry384 a blsModulus)))
        blsCarryShape = true := by
      simp [blsCarryShape, carry384Value, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    rw [hshape]
    right
    refine ⟨carryHalf384 (addCarry384 a blsModulus).1 (addCarry384 a blsModulus).2, ?_⟩
    have he := blsCarryHalfExpr_eval
      (setVarHOLFinite (ofString "s") (carry384Value (addCarry384 a blsModulus)) {post with locals := s.locals})
      (ofString "s") a blsModulus (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    dsimp only [arithEval] at he
    simp [evaluateHOLFiniteState_return, he, Limbs384.toValue, shapeOfHOLExact,
      sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]

theorem blsHalf_tail_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a : Limbs384) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "x") = some a.toValue) :
    (evaluateHOLFiniteState s (.call none (ofString "bls_fp_shr1") [.var .local (ofString "x")])).1 = some .timeOut ∨
      (evaluateHOLFiniteState s (.call none (ofString "bls_fp_shr1") [.var .local (ofString "x")])).1 =
        some (.returned (half384 a).toValue) := by
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "x")] = some [a.toValue] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha]
  let locals := HolFiniteMapExact.empty.update (ofString "x", a.toValue)
  have hlookup : lookupCodeHOLFinite s.code.lookup (ofString "bls_fp_shr1") [a.toValue] =
      some (arithSourceBody Guest.Software.guestFn_bls_fp_shr1, locals, blsU384Shape) := by
    apply arith_one_arg_lookup s.code.lookup (ofString "bls_fp_shr1") (ofString "x") blsU384Shape blsU384Shape _ a.toValue
    · simp [blsU384Shape, Limbs384.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · rw [hc]; exact arith_lookup_bls_fp_shr1
  rw [evaluateHOLFiniteState_call, hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  by_cases hz : s.clock = 0
  · left; simp [hz]
  · rw [if_neg hz]
    have hr := eval_bls_fp_shr1_body (callEntryStateHOLFinite s locals) a
      (by simp [locals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    rw [hr]
    right
    simp [blsU384Shape, Limbs384.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]

theorem blsModHalf_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a : Limbs384) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "x") = some a.toValue) :
    (evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_bls_fp_half_can)).1 = some .timeOut ∨
      ∃ r : Limbs384,
        (evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_bls_fp_half_can)).1 = some (.returned r.toValue) := by
  have hg := blsEvenExpr_eval s (ofString "x") a ha
  dsimp only [arithEval] at hg
  rw [blsModHalf_source_eq, evaluateHOLFiniteState_seq_line780]
  by_cases he : a.toNat % 2 = 0
  · have hfirst : evaluateHOLFiniteState s
        (.ite (inverseEvenExpr (ofString "x"))
          (.call none (ofString "bls_fp_shr1") [.var .local (ofString "x")]) .skip) =
        evaluateHOLFiniteState s (.call none (ofString "bls_fp_shr1") [.var .local (ofString "x")]) := by
      simp [evaluateHOLFiniteState_ite, hg, he]
    rw [hfirst]
    have ht := blsHalf_tail_typed s a hc ha
    rcases hr : evaluateHOLFiniteState s (.call none (ofString "bls_fp_shr1") [.var .local (ofString "x")]) with ⟨res, post⟩
    rw [hr] at ht
    rcases ht with ht | ht
    · dsimp only at ht; subst res; exact Or.inl rfl
    · dsimp only at ht; subst res; exact Or.inr ⟨half384 a, rfl⟩
  · have hfirst : evaluateHOLFiniteState s
        (.ite (inverseEvenExpr (ofString "x"))
          (.call none (ofString "bls_fp_shr1") [.var .local (ofString "x")]) .skip) = (none, s) := by
      simp [evaluateHOLFiniteState_ite, hg, he, evaluateHOLFiniteState_skip]
    rw [hfirst]
    exact blsModHalfOdd_typed s a hc ha

theorem blsModHalf_call_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (coefficient : MlS) (a : Limbs384) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup coefficient = some a.toValue) :
    (evaluateHOLFiniteState s (blsUnaryCall (ofString "bls_fp_half_can") coefficient)).1 = some .timeOut ∨
      ∃ r : Limbs384,
        (evaluateHOLFiniteState s (blsUnaryCall (ofString "bls_fp_half_can") coefficient)).1 = none ∧
        (evaluateHOLFiniteState s (blsUnaryCall (ofString "bls_fp_half_can") coefficient)).2.locals =
          s.locals.update (coefficient, r.toValue) := by
  have ht := blsUnaryCall_typed s (ofString "bls_fp_half_can") coefficient
    (arithSourceBody Guest.Software.guestFn_bls_fp_half_can) a (fun _ => True) hc ha
    arith_lookup_bls_fp_half_can (by
      intro st hcode hl
      rcases blsModHalf_typed st a hcode hl with ht | ⟨r, hr⟩
      · exact Or.inl ht
      · exact Or.inr ⟨r, trivial, hr⟩)
  rcases ht with ht | ⟨r, _, hn, hl⟩
  · exact Or.inl ht
  · exact Or.inr ⟨r, hn, hl⟩
end InitECandidate.Solver.Wave8GuestInv.Arith
