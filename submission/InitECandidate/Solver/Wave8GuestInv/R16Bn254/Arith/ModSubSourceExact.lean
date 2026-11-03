import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModSubExact

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
attribute [local irreducible] wordAddCarryHOL addCarry256 subCarry256

/-- Every successful return of the actual modular subtraction agrees with
its limb arithmetic model. No canonicality hypothesis is needed here. -/
theorem modSub_returned_exact {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b m : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "x") = some a.toValue)
    (hb : s.locals.lookup (ofString "y") = some b.toValue)
    (hm : s.locals.lookup (ofString "m") = some m.toValue)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_mod_sub) =
      (some (.returned ret), post)) :
    ret = (modSub256 a b m).toValue := by
  rw [modSub_source_eq] at hr
  obtain ⟨s1, p1, hl1, hc1, hr1, _⟩ := inverse_lt_decCall_returned
    (ofString "lt") (ofString "x") (ofString "y") a b _ ret hc ha hb hr
  have hx1 : s1.locals.lookup (ofString "x") = some a.toValue := by
    simp [hl1, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "lt" ≠ ofString "x" by decide, show ofString "lt" ≠ ofString "y" by decide, show ofString "lt" ≠ ofString "m" by decide, show ofString "d" ≠ ofString "lt" by decide, show ofString "d" ≠ ofString "m" by decide, show ofString "y" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "y" by decide, ha]
  have hy1 : s1.locals.lookup (ofString "y") = some b.toValue := by
    simp [hl1, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "lt" ≠ ofString "x" by decide, show ofString "lt" ≠ ofString "y" by decide, show ofString "lt" ≠ ofString "m" by decide, show ofString "d" ≠ ofString "lt" by decide, show ofString "d" ≠ ofString "m" by decide, show ofString "y" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "y" by decide, hb]
  obtain ⟨s2, p2, hl2, hc2, hr2, _⟩ := inverse_sub_decCall_returned
    (ofString "d") (ofString "x") (ofString "y") a b _ ret (hc1.trans hc) hx1 hy1 hr1
  apply modSubTail_returned a b m ret (hc2.trans (hc1.trans hc)) _ _ _ hr2
  · simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "lt" ≠ ofString "x" by decide, show ofString "lt" ≠ ofString "y" by decide, show ofString "lt" ≠ ofString "m" by decide, show ofString "d" ≠ ofString "lt" by decide, show ofString "d" ≠ ofString "m" by decide, show ofString "y" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "y" by decide]
  · simp [hl2, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "lt" ≠ ofString "x" by decide, show ofString "lt" ≠ ofString "y" by decide, show ofString "lt" ≠ ofString "m" by decide, show ofString "d" ≠ ofString "lt" by decide, show ofString "d" ≠ ofString "m" by decide, show ofString "y" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "y" by decide]
  · simp [hl2, hl1, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "lt" ≠ ofString "x" by decide, show ofString "lt" ≠ ofString "y" by decide, show ofString "lt" ≠ ofString "m" by decide, show ofString "d" ≠ ofString "lt" by decide, show ofString "d" ≠ ofString "m" by decide, show ofString "y" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "x" by decide, show ofString "m" ≠ ofString "y" by decide, hm]

end InitECandidate.Solver.Wave8GuestInv.Arith
