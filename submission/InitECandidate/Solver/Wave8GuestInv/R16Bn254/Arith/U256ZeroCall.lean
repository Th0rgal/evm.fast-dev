import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256ZeroSemantics

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

theorem u256Zero_decCall_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp arg : MlS) (a : Limbs256) (cont : ProgHOL 64) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup arg = some a.toValue)
    (hr : evaluateHOLFiniteState s
      (.decCall temp .one (ofString "u256_is_zero") [.var .local arg] cont) =
      (some (.returned ret), post)) :
    ∃ resumed inner : PanSemStateFiniteExact 64 F,
      resumed.locals = s.locals.update (temp, .val (.word (if a.toNat = 0 then 1 else 0))) ∧
      resumed.code = s.code ∧ evaluateHOLFiniteState resumed cont = (some (.returned ret), inner) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, _, hrun, _, hlocals, hcode, hcont, _⟩ := arith_decCall_returned hr
  have hvalues : values = [a.toValue] := by
    have hev : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
        [.var .local arg] = some [a.toValue] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha]
    exact Option.some.inj (hargs.symm.trans hev)
  subst values
  rw [hc] at hlk
  have hlookup := arith_one_arg_lookup originalRuntimeCode.lookup (ofString "u256_is_zero")
    (ofString "a") arithU256Shape .one (arithSourceBody Guest.Software.guestFn_u256_is_zero) a.toValue
    (by simp [arithU256Shape, Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    arith_lookup_u256_is_zero
  rw [hlookup] at hlk
  cases hlk
  have he := eval_u256_is_zero_body (callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "a", a.toValue))) a
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  rw [he] at hrun
  have hv : value = .val (.word (if a.toNat = 0 then 1 else 0)) := by
    simpa using (Prod.mk.inj hrun).1.symm
  exact ⟨resumed, inner, by simpa only [hv] using hlocals, hcode, hcont⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
