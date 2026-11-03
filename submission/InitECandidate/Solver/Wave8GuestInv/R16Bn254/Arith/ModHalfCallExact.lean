import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModHalfExact
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseCallFacts

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

theorem modHalf_call_exact_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest left right : MlS) (a b : Limbs256)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup left = some a.toValue)
    (hb : s.locals.lookup right = some b.toValue)
    (hr : evaluateHOLFiniteState s
      (.call (some (some (.local, dest), none)) (ofString "mod_half")
        [.var .local left, .var .local right]) = (none, post)) :
    post.locals = s.locals.update (dest, (modHalf256 a b).toValue) := by
  obtain ⟨values, body, callee, rs, value, bpost, hargs, hlk, _, hrun, _, hlocals, _⟩ := arith_call_local_none hr
  have hvalues : values = [a.toValue, b.toValue] := by
    have hev : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
        [.var .local left, .var .local right] = some [a.toValue, b.toValue] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb]
    exact Option.some.inj (hargs.symm.trans hev)
  subst values
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "mod_half") (ofString "x") (ofString "m")
    arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_mod_half) a.toValue b.toValue
    (by decide) arith_lookup_mod_half hlk
  have ht := modHalf_exact
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "x", a.toValue)).update
      (ofString "m", b.toValue))) a b hc
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "x" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  rw [hrun] at ht
  have hv : value = (modHalf256 a b).toValue := by
    rcases ht with ht | ht
    · cases ht
    · simpa using ht
  simpa [hv] using hlocals

end InitECandidate.Solver.Wave8GuestInv.Arith
