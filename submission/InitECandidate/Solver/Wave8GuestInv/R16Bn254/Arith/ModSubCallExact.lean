import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModSubSourceExact
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ThreeArgLookup
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseSubtractTail

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
attribute [local irreducible] wordAddCarryHOL addCarry256 subCarry256

theorem modSub_call_exact_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest left right modulus : MlS) (a b m : Limbs256)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup left = some a.toValue)
    (hb : s.locals.lookup right = some b.toValue)
    (hm : s.locals.lookup modulus = some m.toValue)
    (hr : evaluateHOLFiniteState s
      (.call (some (some (.local, dest), none)) (ofString "mod_sub")
        [.var .local left, .var .local right, .var .local modulus]) = (none, post)) :
    post.locals = s.locals.update (dest, (modSub256 a b m).toValue) := by
  obtain ⟨values, body, callee, rs, value, bpost, hargs, hlk, _, hrun, _, hlocals, _⟩ :=
    arith_call_local_none hr
  have hvalues : values = [a.toValue, b.toValue, m.toValue] := by
    have hev : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
        [.var .local left, .var .local right, .var .local modulus] =
        some [a.toValue, b.toValue, m.toValue] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb, hm]
    exact Option.some.inj (hargs.symm.trans hev)
  subst values
  rw [hc] at hlk
  have hlookup := arith_three_arg_lookup originalRuntimeCode.lookup
    (ofString "mod_sub") (ofString "x") (ofString "y") (ofString "m")
    arithU256Shape arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_mod_sub) a.toValue b.toValue m.toValue
    (by decide) (by decide) (by decide)
    (by simp [arithU256Shape, Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    (by simp [arithU256Shape, Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    (by simp [arithU256Shape, Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    arith_lookup_mod_sub
  rw [hlookup] at hlk
  cases hlk
  have hv := modSub_returned_exact (s := callEntryStateHOLFinite s
      (((HolFiniteMapExact.empty.update (ofString "x", a.toValue)).update
        (ofString "y", b.toValue)).update (ofString "m", m.toValue))) a b m value hc
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "lt" ≠ ofString "x" by decide, show ofString "lt" ≠ ofString "y" by decide, show ofString "lt" ≠ ofString "m" by decide, show ofString "d" ≠ ofString "lt" by decide, show ofString "d" ≠ ofString "m" by decide, show ofString "y" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "y" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "lt" ≠ ofString "x" by decide, show ofString "lt" ≠ ofString "y" by decide, show ofString "lt" ≠ ofString "m" by decide, show ofString "d" ≠ ofString "lt" by decide, show ofString "d" ≠ ofString "m" by decide, show ofString "y" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "y" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "lt" ≠ ofString "x" by decide, show ofString "lt" ≠ ofString "y" by decide, show ofString "lt" ≠ ofString "m" by decide, show ofString "d" ≠ ofString "lt" by decide, show ofString "d" ≠ ofString "m" by decide, show ofString "y" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "y" by decide]) hrun
  simpa [hv] using hlocals

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
