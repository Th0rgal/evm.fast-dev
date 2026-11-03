import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.P256CarryBody

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

attribute [local irreducible] wordAddCarryHOL

def p256Borrow (r : Limbs256) : BitVec 64 :=
  if r.toNat < p256Modulus.toNat then 1 else 0

def p256PositiveBody : ProgHOL 64 :=
  .decCall (ofString "ltp") .one (ofString "u256_lt")
    [.var .local (ofString "r"), p256Literal]
    (.seq (.call (some (some (.local, ofString "r"), none)) (ofString "u256_sub")
      [.var .local (ofString "r"), p256Literal])
      (.assign .local (ofString "c") (.op .sub [.var .local (ofString "c"), .var .local (ofString "ltp")])))

/-- Successful lookup supplies the four-word input; comparison and subtraction give the exact borrow. -/
theorem p256PositiveBody_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {c : BitVec 64} (hcode : s.code = originalRuntimeCode)
    (hc : s.locals.lookup (ofString "c") = some (.val (.word c)))
    (h : evaluateHOLFiniteState s p256PositiveBody = (none, post)) :
    ∃ r : Limbs256,
      s.locals.lookup (ofString "r") = some r.toValue ∧
      post.locals.lookup (ofString "r") = some (subCarry256 r p256Modulus).1.toValue ∧
      post.locals.lookup (ofString "c") = some (.val (.word (c - p256Borrow r))) := by
  unfold p256PositiveBody at h
  obtain ⟨vals, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, _, hrun, _, hl, hrescode, hcont, hpost⟩ := arith_decCall_none h
  cases hr : s.locals.lookup (ofString "r") with
  | none => simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hr] at hargs
  | some rv =>
    have hvals : vals = [rv, p256Modulus.toValue] := by
      have hev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.var .local (ofString "r"), p256Literal] = some [rv, p256Modulus.toValue] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hr,
          p256Literal, p256Modulus, Limbs256.toValue]
      exact Option.some.inj (hargs.symm.trans hev)
    subst vals
    rw [hcode] at hlk
    obtain ⟨hshape, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
      originalRuntimeCode.lookup (ofString "u256_lt") (ofString "a") (ofString "b")
      arithU256Shape arithU256Shape .one
      (arithSourceBody Guest.Software.guestFn_u256_lt) rv p256Modulus.toValue
      (by decide) arith_lookup_u256_lt hlk
    obtain ⟨r, rfl⟩ := arith_shape_u256 hshape
    have hret := eval_u256_lt_body
      (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", r.toValue)).update
        (ofString "b", p256Modulus.toValue))) r p256Modulus
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "b" ≠ ofString "a" by decide])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    have hv : value = .val (.word (p256Borrow r)) := by
      rw [hret] at hrun
      simpa [p256Borrow, lt256_correct] using (Prod.mk.inj hrun).1.symm
    subst value
    have hsr : resumed.locals.lookup (ofString "r") = some r.toValue := by
      rw [hl]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hr,
        show ofString "ltp" ≠ ofString "r" by decide]
    have hsc : resumed.locals.lookup (ofString "c") = some (.val (.word c)) := by
      rw [hl]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hc,
        show ofString "ltp" ≠ ofString "c" by decide]
    have hsltp : resumed.locals.lookup (ofString "ltp") = some (.val (.word (p256Borrow r))) := by
      rw [hl]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    obtain ⟨mid, hsub, hassign⟩ := arith_seq_none hcont
    obtain ⟨subvals, subbody, subcallee, subrs, subval, subpost,
      hsubargs, hsublk, _, hsubrun, _, hmid, _⟩ := arith_call_local_none hsub
    have hsubvals : subvals = [r.toValue, p256Modulus.toValue] := by
      have hev : evalListHOLFinite resumed (h := fun a => Classical.propDecidable (resumed.memaddrs a))
          [.var .local (ofString "r"), p256Literal] = some [r.toValue, p256Modulus.toValue] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsr,
          p256Literal, p256Modulus, Limbs256.toValue]
      exact Option.some.inj (hsubargs.symm.trans hev)
    subst subvals
    rw [hrescode, hcode] at hsublk
    obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
      originalRuntimeCode.lookup (ofString "u256_sub") (ofString "a") (ofString "b")
      arithU256Shape arithU256Shape arithU256Shape
      (arithSourceBody Guest.Software.guestFn_u256_sub) r.toValue p256Modulus.toValue
      (by decide) arith_lookup_u256_sub hsublk
    obtain ⟨ret, hsubret, _⟩ := eval_u256_sub_body
      (callEntryStateHOLFinite resumed ((HolFiniteMapExact.empty.update (ofString "a", r.toValue)).update
        (ofString "b", p256Modulus.toValue))) r p256Modulus
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "b" ≠ ofString "a" by decide])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    have hsv : subval = (subCarry256 r p256Modulus).1.toValue := by
      change evaluateHOLFiniteState _ (subSourceBody Guest.Software.guestFn_u256_sub) = _ at hsubrun
      rw [hsubret] at hsubrun
      simpa using (Prod.mk.inj hsubrun).1.symm
    subst subval
    have hmc : mid.locals.lookup (ofString "c") = some (.val (.word c)) := by
      rw [hmid]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsc,
        show ofString "r" ≠ ofString "c" by decide]
    have hmltp : mid.locals.lookup (ofString "ltp") = some (.val (.word (p256Borrow r))) := by
      rw [hmid]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hsltp,
        show ofString "r" ≠ ofString "ltp" by decide]
    have heval : evaluateHOLFiniteState mid
        (.assign .local (ofString "c") (.op .sub [.var .local (ofString "c"), .var .local (ofString "ltp")])) =
        (none, setVarHOLFinite (ofString "c") (.val (.word (c - p256Borrow r))) mid) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hmc, hmltp,
        wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact,
        lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
    rw [heval] at hassign
    have hi := (Prod.mk.inj hassign).2
    subst inner
    refine ⟨r, rfl, ?_, ?_⟩
    all_goals rw [hpost]
    all_goals simp [show ofString "r" ≠ ofString "ltp" by decide,
      show ofString "c" ≠ ofString "ltp" by decide, InitECandidate.Solver.PanRunBounded.resVarEq_lookup,
      setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hmid,
      show ofString "ltp" ≠ ofString "r" by decide,
      show ofString "ltp" ≠ ofString "c" by decide,
      show ofString "c" ≠ ofString "r" by decide]
end InitECandidate.Solver.Wave8GuestInv.Arith
