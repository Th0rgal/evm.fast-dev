import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.HalfNormalize

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2500000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
attribute [local irreducible] wordAddCarryHOL subCarry256

theorem arith_lookup_return_shape
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fname : MlS) (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (rs : ShapeHOL)
    (hinstalled : code fname = some (params, body, rs))
    (values : List (ValueHOL 64)) (found : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (foundRs : ShapeHOL)
    (hfound : lookupCodeHOLFinite code fname values = some (found, callee, foundRs)) :
    foundRs = rs := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
  split at hfound
  · cases hfound
  · rename_i _ _ _ hraw
    unfold lookupCodeHOLExact at hraw
    rw [hinstalled] at hraw
    dsimp only at hraw
    split at hraw
    · cases hraw
      cases hfound
      rfl
    · cases hraw

theorem arith_call_local_u256_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest fname : MlS) (args : List (ExpHOL 64))
    (params : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hi : originalRuntimeCode.lookup fname = some (params, body, arithU256Shape))
    (hr : evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) fname args) = (none, post)) :
    ∃ r : Limbs256, post.locals = s.locals.update (dest, r.toValue) := by
  obtain ⟨values, found, callee, rs, value, bpost, _, hlk, _, _, hshape, hlocals, _⟩ := arith_call_local_none hr
  have hrs := arith_lookup_return_shape s.code.lookup fname params body arithU256Shape
    (by rw [hc]; exact hi) values found callee rs hlk
  subst rs
  have hreverse : shapeEqHOL arithU256Shape (shapeOfHOLExact value) = true :=
    (shapeEqHOL_eq_true _ _).mpr ((shapeEqHOL_eq_true _ _).mp hshape).symm
  obtain ⟨r, rfl⟩ := arith_shape_u256 hreverse
  exact ⟨r, hlocals⟩

theorem inverse_sub_call_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest left right : MlS) (a b : Limbs256)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup left = some a.toValue)
    (hb : s.locals.lookup right = some b.toValue)
    (hr : evaluateHOLFiniteState s
      (.call (some (some (.local, dest), none)) (ofString "u256_sub")
        [.var .local left, .var .local right]) = (none, post)) :
    post.locals = s.locals.update (dest, (subCarry256 a b).1.toValue) := by
  obtain ⟨values, body, callee, rs, value, bpost, hargs, hlk, _, hrun, _, hlocals, _⟩ := arith_call_local_none hr
  have hvalues : values = [a.toValue, b.toValue] := by
    have hev : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
        [.var .local left, .var .local right] = some [a.toValue, b.toValue] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
    exact Option.some.inj (hargs.symm.trans hev)
  subst values
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "u256_sub") (ofString "a") (ofString "b")
    arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_u256_sub) a.toValue b.toValue
    (by decide) arith_lookup_u256_sub hlk
  obtain ⟨ret, hret, _⟩ := eval_u256_sub_body
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update
      (ofString "b", b.toValue))) a b
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  change evaluateHOLFiniteState _ (subSourceBody Guest.Software.guestFn_u256_sub) = _ at hrun
  rw [hret] at hrun
  have hv : value = (subCarry256 a b).1.toValue := by simpa using (Prod.mk.inj hrun).1.symm
  simpa [hv] using hlocals

theorem inverse_lt_decCall_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp left right : MlS) (a b : Limbs256) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup left = some a.toValue)
    (hb : s.locals.lookup right = some b.toValue)
    (hr : evaluateHOLFiniteState s
      (.decCall temp .one (ofString "u256_lt") [.var .local left, .var .local right] cont) = (none, post)) :
    ∃ resumed inner : PanSemStateFiniteExact 64 F,
      resumed.locals = s.locals.update (temp, .val (.word (if a.toNat < b.toNat then 1 else 0))) ∧
      resumed.code = s.code ∧ evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp, s.locals.lookup temp) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, _, hrun, _, hlocals, hcode, hcont, hpost⟩ := arith_decCall_none hr
  have hvalues : values = [a.toValue, b.toValue] := by
    have hev : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
        [.var .local left, .var .local right] = some [a.toValue, b.toValue] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
    exact Option.some.inj (hargs.symm.trans hev)
  subst values
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "u256_lt") (ofString "a") (ofString "b")
    arithU256Shape arithU256Shape .one
    (arithSourceBody Guest.Software.guestFn_u256_lt) a.toValue b.toValue
    (by decide) arith_lookup_u256_lt hlk
  have hret := eval_u256_lt_body
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update
      (ofString "b", b.toValue))) a b
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  rw [hret] at hrun
  have hv : value = .val (.word (if a.toNat < b.toNat then 1 else 0)) := by
    simpa [lt256_correct] using (Prod.mk.inj hrun).1.symm
  refine ⟨resumed, inner, ?_, hcode, hcont, hpost⟩
  simpa [hv] using hlocals

end InitECandidate.Solver.Wave8GuestInv.Arith
