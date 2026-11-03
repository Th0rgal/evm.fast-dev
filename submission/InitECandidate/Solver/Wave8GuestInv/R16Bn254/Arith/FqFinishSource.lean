import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqReductionSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryPacking

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

/-- Successful execution of the actual packing declaration and final reduction
returns the single-subtraction result for the eight output digits. -/
theorem fqMulFinish_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (d : Fin 8 → BitVec 64) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hd : ∀ i, (d i).toNat < 2 ^ 32)
    (h0 : s.locals.lookup (ofString "u0") = some (.val (.word (d 0))))
    (h1 : s.locals.lookup (ofString "u1") = some (.val (.word (d 1))))
    (h2 : s.locals.lookup (ofString "u2") = some (.val (.word (d 2))))
    (h3 : s.locals.lookup (ofString "u3") = some (.val (.word (d 3))))
    (h4 : s.locals.lookup (ofString "u4") = some (.val (.word (d 4))))
    (h5 : s.locals.lookup (ofString "u5") = some (.val (.word (d 5))))
    (h6 : s.locals.lookup (ofString "u6") = some (.val (.word (d 6))))
    (h7 : s.locals.lookup (ofString "c") = some (.val (.word (d 7))))
    (he : evaluateHOLFiniteState s fqMulFinish = (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧
      out.toNat = montFinalReduce (montRadix8 (fun i => (d i).toNat)) fqModulus.toNat := by
  rw [fqMulFinish_source_eq] at he
  obtain ⟨value, hinit, hshape, inner, hbody⟩ := arith_dec_returned he
  have hv : value = (montPackLimbs d).toValue := by
    simpa [evalHOLFinite, evalHOLExact, evalListHOLExact, montVar, h0, h1, h2, h3,
      h4, h5, h6, h7, wordOpHOL, wordOp, wordShiftHOL, valueIsWord, valueWord,
      montPackLimbs, Limbs256.toValue, OrOp.or] using hinit.symm
  subst value
  obtain ⟨out, hret, hnat⟩ := fqReduction_returned_exact
    (s := setVarHOLFinite (ofString "r") (montPackLimbs d).toValue s)
    (montPackLimbs d) ret
    (by simpa [setVarHOLFinite] using hc)
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hbody
  rw [montPackLimbs_toNat d hd] at hnat
  exact ⟨out, hret, hnat⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
