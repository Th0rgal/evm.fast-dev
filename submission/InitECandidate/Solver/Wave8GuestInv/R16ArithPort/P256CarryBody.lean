import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.U256CallFacts

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

attribute [local irreducible] wordAddCarryHOL

def p256Literal : ExpHOL 64 :=
  .rstruct [.const 18446744073709551615, .const 4294967295, .const 0, .const 18446744069414584321]

def p256NegativeTail : ProgHOL 64 :=
  .seq (.assign .local (ofString "r")
    (.rstruct [.rfield 0 (.var .local (ofString "sa")),
      .rfield 1 (.var .local (ofString "sa")),
      .rfield 2 (.var .local (ofString "sa")),
      .rfield 3 (.var .local (ofString "sa"))]))
    (.assign .local (ofString "c")
      (.op .add [.var .local (ofString "c"), .rfield 4 (.var .local (ofString "sa"))]))

def p256NegativeBody : ProgHOL 64 :=
  .decCall (ofString "sa") (.comb [.one, .one, .one, .one, .one]) (ofString "u256_add_carry")
    [.var .local (ofString "r"), p256Literal] p256NegativeTail

private theorem negative_tail_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (r : Limbs256) (c : BitVec 64)
    (hr : s.locals.lookup (ofString "r") = some r.toValue)
    (hc : s.locals.lookup (ofString "c") = some (.val (.word c)))
    (hsa : s.locals.lookup (ofString "sa") = some (addCarry256Value r p256Modulus)) :
    evaluateHOLFiniteState s p256NegativeTail =
      (none, setVarHOLFinite (ofString "c") (.val (.word (c + (addCarry256 r p256Modulus).2)))
        (setVarHOLFinite (ofString "r") (addCarry256 r p256Modulus).1.toValue s)) := by
  have hrc : ofString "r" ≠ ofString "c" := by decide
  have hrsa : ofString "r" ≠ ofString "sa" := by decide
  simp [p256NegativeTail, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign,
    evalHOLExact, evalListHOLExact, hr, hc, hsa, addCarry256Value,
    Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL,
    isValidValueHOLExact, lookupKvarHOLExact, setKvarHOLFinite, setVarHOLFinite,
    HolFiniteMapExact.lookup_update, FUPDATE, hrc, hrsa, wordOpHOL, wordOp, valueIsWord, valueWord]

/-- A continuing iteration validates its initial four-word value and has the exact carry effect. -/
theorem p256NegativeBody_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {c : BitVec 64} (hcode : s.code = originalRuntimeCode)
    (hc : s.locals.lookup (ofString "c") = some (.val (.word c)))
    (h : evaluateHOLFiniteState s p256NegativeBody = (none, post)) :
    ∃ r : Limbs256,
      s.locals.lookup (ofString "r") = some r.toValue ∧
      post.locals.lookup (ofString "r") = some (addCarry256 r p256Modulus).1.toValue ∧
      post.locals.lookup (ofString "c") = some (.val (.word (c + (addCarry256 r p256Modulus).2))) := by
  unfold p256NegativeBody at h
  obtain ⟨vals, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, _, hrun, _, hl, _, hcont, hpost⟩ := arith_decCall_none h
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
      originalRuntimeCode.lookup (ofString "u256_add_carry") (ofString "a") (ofString "b")
      arithU256Shape arithU256Shape (.comb [.one, .one, .one, .one, .one])
      (arithSourceBody Guest.Software.guestFn_u256_add_carry) rv p256Modulus.toValue
      (by decide) arith_lookup_u256_add_carry hlk
    obtain ⟨r, rfl⟩ := arith_shape_u256 hshape
    obtain ⟨ret, hret, _⟩ := eval_u256_add_carry_body
      (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", r.toValue)).update
        (ofString "b", p256Modulus.toValue))) r p256Modulus
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "b" ≠ ofString "a" by decide])
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    have hv : value = addCarry256Value r p256Modulus := by
      rw [hret] at hrun
      simpa using (Prod.mk.inj hrun).1.symm
    subst value
    have hsr : resumed.locals.lookup (ofString "r") = some r.toValue := by
      rw [hl]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hr,
        show ofString "sa" ≠ ofString "r" by decide]
    have hsc : resumed.locals.lookup (ofString "c") = some (.val (.word c)) := by
      rw [hl]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hc,
        show ofString "sa" ≠ ofString "c" by decide]
    have hssa : resumed.locals.lookup (ofString "sa") = some (addCarry256Value r p256Modulus) := by
      rw [hl]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [negative_tail_eval resumed r c hsr hsc hssa] at hcont
    have hi := (Prod.mk.inj hcont).2
    subst inner
    refine ⟨r, rfl, ?_, ?_⟩
    all_goals rw [hpost]
    all_goals simp [show ofString "r" ≠ ofString "sa" by decide,
      show ofString "c" ≠ ofString "sa" by decide, InitECandidate.Solver.PanRunBounded.resVarEq_lookup,
      setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "sa" ≠ ofString "r" by decide,
      show ofString "sa" ≠ ofString "c" by decide,
      show ofString "c" ≠ ofString "r" by decide]
end InitECandidate.Solver.Wave8GuestInv.Arith
