import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ReturnedFacts
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseCallFacts
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256AddSemantics
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.TailReturnedFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2500000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
attribute [local irreducible] wordAddCarryHOL subCarry256

theorem arith_lt_decCall_exprs_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp : MlS) (args : List (ExpHOL 64)) (a b : Limbs256) (cont : ProgHOL 64) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (heargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args =
      some [a.toValue, b.toValue])
    (hr : evaluateHOLFiniteState s
      (.decCall temp .one (ofString "u256_lt") args cont) = (some (.returned ret), post)) :
    ∃ resumed inner : PanSemStateFiniteExact 64 F,
      resumed.locals = s.locals.update (temp, .val (.word (if a.toNat < b.toNat then 1 else 0))) ∧
      resumed.code = s.code ∧ evaluateHOLFiniteState resumed cont = (some (.returned ret), inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp, s.locals.lookup temp) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, _, hrun, _, hlocals, hcode, hcont, hpost⟩ := arith_decCall_returned hr
  have hvalues : values = [a.toValue, b.toValue] := Option.some.inj (hargs.symm.trans heargs)
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

theorem arith_sub_tailCall_exprs_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (args : List (ExpHOL 64)) (a b : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (heargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args =
      some [a.toValue, b.toValue])
    (hr : evaluateHOLFiniteState s (.call none (ofString "u256_sub") args) = (some (.returned ret), post)) :
    ret = (subCarry256 a b).1.toValue := by
  obtain ⟨values, body, callee, rs, bpost, hargs, hlk, _, hrun, _⟩ := arith_tailCall_returned hr
  have hvalues : values = [a.toValue, b.toValue] := Option.some.inj (hargs.symm.trans heargs)
  subst values
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "u256_sub") (ofString "a") (ofString "b")
    arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_u256_sub) a.toValue b.toValue
    (by decide) arith_lookup_u256_sub hlk
  obtain ⟨subPost, hret, _⟩ := eval_u256_sub_body
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update
      (ofString "b", b.toValue))) a b
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  change evaluateHOLFiniteState _ (subSourceBody Guest.Software.guestFn_u256_sub) = _ at hrun
  rw [hret] at hrun
  simpa using (Prod.mk.inj hrun).1.symm

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
