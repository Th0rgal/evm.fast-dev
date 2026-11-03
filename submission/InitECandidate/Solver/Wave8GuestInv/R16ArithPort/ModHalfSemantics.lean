import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.InverseHalfSemantics

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
attribute [local irreducible] wordAddCarryHOL addCarry256

private theorem modhalf_two_arg_lookup {width : Nat} [NeZero width]
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

def inverseCarryHalfExpr (counter : MlS) : ExpHOL 64 :=
  .rstruct [
    .op .or [.shift .lsr (.rfield 0 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 1 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 1 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 2 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 2 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 3 (.var .local counter)) (.const 63)],
    .op .or [.shift .lsr (.rfield 3 (.var .local counter)) (.const 1),
      .shift .lsl (.rfield 4 (.var .local counter)) (.const 63)]]

def carryHalf256 (a : Limbs256) (carry : BitVec 64) : Limbs256 :=
  ⟨halfWord256 a.l0 a.l1, halfWord256 a.l1 a.l2,
    halfWord256 a.l2 a.l3, halfWord256 a.l3 carry⟩

theorem inverseCarryHalfExpr_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a b : Limbs256)
    (hl : s.locals.lookup counter = some (addCarry256Value a b)) :
    arithEval s (inverseCarryHalfExpr counter) =
      some (carryHalf256 (addCarry256 a b).1 (addCarry256 a b).2).toValue := by
  simp [inverseCarryHalfExpr, arithEval, evalHOLExact, evalListHOLExact, hl,
    addCarry256Value, Limbs256.toValue, wordShiftHOL, wordOpHOL, wordOp,
    valueIsWord, valueWord, carryHalf256, halfWord256, OrOp.or]

def modHalfOddBody : ProgHOL 64 :=
  .decCall (ofString "s") (.comb [.one, .one, .one, .one, .one])
    (ofString "u256_add_carry") [.var .local (ofString "x"), .var .local (ofString "m")]
    (.return (inverseCarryHalfExpr (ofString "s")))

theorem modHalf_source_eq : arithSourceBody Guest.Software.guestFn_mod_half =
    .seq (.ite (inverseEvenExpr (ofString "x"))
      (.return (inverseHalfExpr (ofString "x"))) .skip) modHalfOddBody := rfl

/-- With typed operands, the odd branch can only return a four-word value or
exhaust its clock at the addition call; malformed-value errors are impossible. -/
theorem modHalfOdd_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : Limbs256) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "x") = some a.toValue)
    (hb : s.locals.lookup (ofString "m") = some b.toValue) :
    (evaluateHOLFiniteState s modHalfOddBody).1 = some .timeOut ∨
      ∃ r : Limbs256, (evaluateHOLFiniteState s modHalfOddBody).1 = some (.returned r.toValue) := by
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "x"), .var .local (ofString "m")] = some [a.toValue, b.toValue] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
  let locals := (HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update (ofString "b", b.toValue)
  have hlookup : lookupCodeHOLFinite s.code.lookup (ofString "u256_add_carry") [a.toValue, b.toValue] =
      some (arithSourceBody Guest.Software.guestFn_u256_add_carry, locals,
        .comb [.one, .one, .one, .one, .one]) := by
    apply modhalf_two_arg_lookup s.code.lookup (ofString "u256_add_carry")
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
    refine ⟨carryHalf256 (addCarry256 a b).1 (addCarry256 a b).2, ?_⟩
    have he := inverseCarryHalfExpr_eval
      (setVarHOLFinite (ofString "s") (addCarry256Value a b) {post with locals := s.locals})
      (ofString "s") a b (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    dsimp only [arithEval] at he
    simp [evaluateHOLFiniteState_return, he, Limbs256.toValue, shapeOfHOLExact,
      sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]

theorem modHalf_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : Limbs256) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "x") = some a.toValue)
    (hb : s.locals.lookup (ofString "m") = some b.toValue) :
    (evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_mod_half)).1 = some .timeOut ∨
      ∃ r : Limbs256,
        (evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_mod_half)).1 = some (.returned r.toValue) := by
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
    exact Or.inr ⟨half256 a, rfl⟩
  · have hfirst : evaluateHOLFiniteState s
        (.ite (inverseEvenExpr (ofString "x")) (.return (inverseHalfExpr (ofString "x"))) .skip) =
        (none, s) := by
      simp [evaluateHOLFiniteState_ite, hg, he, evaluateHOLFiniteState_skip]
    rw [hfirst]
    exact modHalfOdd_typed s a b hc ha hb

theorem arith_lookup_mod_half :
    originalRuntimeCode.lookup (ofString "mod_half") =
      some ([(ofString "x", arithU256Shape), (ofString "m", arithU256Shape)],
        arithSourceBody Guest.Software.guestFn_mod_half, arithU256Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 158 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mod_half) rfl

def modHalfCall (coefficient : MlS) : ProgHOL 64 :=
  .call (some (some (.local, coefficient), none)) (ofString "mod_half")
    [.var .local coefficient, .var .local (ofString "m")]

theorem modHalf_call_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (coefficient : MlS) (a b : Limbs256) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup coefficient = some a.toValue)
    (hb : s.locals.lookup (ofString "m") = some b.toValue) :
    (evaluateHOLFiniteState s (modHalfCall coefficient)).1 = some .timeOut ∨
      ∃ r : Limbs256,
        (evaluateHOLFiniteState s (modHalfCall coefficient)).1 = none ∧
        (evaluateHOLFiniteState s (modHalfCall coefficient)).2.locals =
          s.locals.update (coefficient, r.toValue) := by
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local coefficient, .var .local (ofString "m")] = some [a.toValue, b.toValue] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
  let locals := (HolFiniteMapExact.empty.update (ofString "x", a.toValue)).update (ofString "m", b.toValue)
  have hlookup : lookupCodeHOLFinite s.code.lookup (ofString "mod_half") [a.toValue, b.toValue] =
      some (arithSourceBody Guest.Software.guestFn_mod_half, locals, arithU256Shape) := by
    apply modhalf_two_arg_lookup s.code.lookup (ofString "mod_half")
      (ofString "x") (ofString "m") arithU256Shape arithU256Shape arithU256Shape
      (arithSourceBody Guest.Software.guestFn_mod_half) a.toValue b.toValue (by decide)
    · simp [arithU256Shape, Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [arithU256Shape, Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · rw [hc]
      exact arith_lookup_mod_half
  unfold modHalfCall
  rw [evaluateHOLFiniteState_call, hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  by_cases hz : s.clock = 0
  · left
    simp [hz]
  · rw [if_neg hz]
    have ht := modHalf_typed (callEntryStateHOLFinite s locals) a b hc
      (by simp [locals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "m" ≠ ofString "x" by decide])
      (by simp [locals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s locals)
        (arithSourceBody Guest.Software.guestFn_mod_half) with ⟨res, post⟩
    rw [hrun] at ht
    rcases ht with ht | ⟨r, hr⟩
    · dsimp only at ht
      subst res
      exact Or.inl rfl
    · dsimp only at hr
      subst res
      right
      refine ⟨r, ?_, ?_⟩
      all_goals simp [arithU256Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL,
        Limbs256.toValue, isValidValueHOLExact, lookupKvarHOLExact, ha,
        setKvarHOLFinite, setVarHOLFinite]
end InitECandidate.Solver.Wave8GuestInv.Arith
