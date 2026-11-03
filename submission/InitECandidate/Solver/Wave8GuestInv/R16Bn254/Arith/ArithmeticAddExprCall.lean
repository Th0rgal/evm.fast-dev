import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ArithmeticReturnCalls

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
attribute [local irreducible] wordAddCarryHOL subCarry256

theorem arith_add_call_exprs_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest : MlS) (args : List (ExpHOL 64)) (a b : Limbs256)
    (hc : s.code = originalRuntimeCode)
    (heargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args =
      some [a.toValue, b.toValue])
    (hr : evaluateHOLFiniteState s
      (.call (some (some (.local, dest), none)) (ofString "u256_add")
        args) = (none, post)) :
    post.locals = s.locals.update (dest, (addCarry256 a b).1.toValue) := by
  obtain ⟨values, body, callee, rs, value, bpost, hargs, hlk, _, hrun, _, hlocals, _⟩ := arith_call_local_none hr
  have hvalues : values = [a.toValue, b.toValue] := Option.some.inj (hargs.symm.trans heargs)
  subst values
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "u256_add") (ofString "a") (ofString "b")
    arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_u256_add) a.toValue b.toValue
    (by decide) arith_lookup_u256_add hlk
  obtain ⟨ret, hret, _⟩ := eval_u256_add_body
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", a.toValue)).update
      (ofString "b", b.toValue))) a b
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  change evaluateHOLFiniteState _ (arithSourceBody Guest.Software.guestFn_u256_add) = _ at hrun
  rw [hret] at hrun
  have hv : value = (addCarry256 a b).1.toValue := by simpa using (Prod.mk.inj hrun).1.symm
  simpa [hv] using hlocals

end InitECandidate.Solver.Wave8GuestInv.Arith
