import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseLoopCorrect
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseLoopNoFallthrough
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModinvLeaf

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

def inverseOne256 : Limbs256 := ⟨1,0,0,0⟩
def inverseZero256 : Limbs256 := ⟨0,0,0,0⟩

theorem inverseInitBody_returned_correct {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a m : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some a.toValue)
    (hm : s.locals.lookup (ofString "m") = some m.toValue)
    (hmodd : m.toNat % 2 = 1) (hmgt : 1 < m.toNat)
    (hr : evaluateHOLFiniteState s inverseInitBody = (some (.returned ret), post)) :
    ∃ x : Limbs256, ret = x.toValue ∧ x.toNat < m.toNat ∧
      InverseCongruence a.toNat m.toNat 1 x.toNat := by
  unfold inverseInitBody at hr
  obtain ⟨u, heu, _, p1, h1⟩ := arith_dec_returned hr
  have hu : u = a.toValue := by simpa [evalHOLFinite, evalHOLExact, ha] using heu.symm
  subst u
  obtain ⟨v, hev, _, p2, h2⟩ := arith_dec_returned h1
  have hv : v = m.toValue := by
    simpa [evalHOLFinite, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "u" ≠ ofString "m" by decide, hm] using hev.symm
  subst v
  obtain ⟨x1, hex1, _, p3, h3⟩ := arith_dec_returned h2
  have hx1 : x1 = inverseOne256.toValue := by
    simpa [evalHOLFinite, evalHOLExact, evalListHOLExact, inverseOneExpr,
      inverseOne256, Limbs256.toValue] using hex1.symm
  subst x1
  obtain ⟨x2, hex2, _, p4, h4⟩ := arith_dec_returned h3
  have hx2 : x2 = inverseZero256.toValue := by
    simpa [evalHOLFinite, evalHOLExact, evalListHOLExact, inverseZeroExpr,
      inverseZero256, Limbs256.toValue] using hex2.symm
  subst x2
  rcases arith_seq_returned h4 with hloop | ⟨mid, hnone, _⟩
  · have hq : (InverseLocals.mk a m inverseOne256 inverseZero256 m).Matches
        (setVarHOLFinite (ofString "x2") inverseZero256.toValue
          (setVarHOLFinite (ofString "x1") inverseOne256.toValue
            (setVarHOLFinite (ofString "v") m.toValue (setVarHOLFinite (ofString "u") a.toValue s)))) := by
      simp [InverseLocals.Matches, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString]
      simpa [ofString] using hm
    have hi : (InverseLocals.mk a m inverseOne256 inverseZero256 m).CoefficientInvariant a.toNat := by
      have hh := inverseCongruence_init a.toNat m.toNat
      refine ⟨?_, ?_, ?_, ?_, hmodd⟩
      · simpa [inverseOne256, Limbs256.toNat] using hh.1
      · simpa [inverseZero256, Limbs256.toNat] using hh.2
      · simpa [inverseOne256, Limbs256.toNat] using hmgt
      · simpa [inverseZero256, Limbs256.toNat] using (show 0 < m.toNat by omega)
    exact inverseOuterLoop_returned_correct
      (setVarHOLFinite (ofString "x2") inverseZero256.toValue
        (setVarHOLFinite (ofString "x1") inverseOne256.toValue
          (setVarHOLFinite (ofString "v") m.toValue (setVarHOLFinite (ofString "u") a.toValue s))))
      _ a.toNat _ ret hc hq hi hloop
  · exact False.elim (inverseOuterLoop_not_none _ (congrArg Prod.fst hnone))

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
