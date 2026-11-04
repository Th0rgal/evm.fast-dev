import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeMemory

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem fqDegreeBody_zero {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (coefficients : Nat → Limbs256) (n : Nat)
    (hpos : 0 < n) (hn : n ≤ 13) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word base)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 n))))
    (halign : base.toNat % 8 = 0) (hbound : base.toNat + 416 ≤ 2 ^ 64)
    (hd : DomainPolynomial s.memaddrs base) (hm : MemoryPolynomial s.memory base coefficients)
    (hr : evaluateHOLFiniteState s fqDegreeBody = (none, post)) :
    (coefficients (n - 1)).toNat = 0 := by
  unfold fqDegreeBody at hr
  rw [evaluateHOLFiniteState_seq_line780, fqDegree_decrement s (BitVec.ofNat 64 n) hi,
    degreeIndex_decrement n hpos hn] at hr
  let next := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (n - 1)))) s
  have ha' : next.locals.lookup (ofString "a") = some (.val (.word base)) := by
    simpa [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "a" by decide] using ha
  have hi' : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (n - 1)))) := by
    simp [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hj : n - 1 < 13 := by omega
  obtain ⟨haj,hbj⟩ := coefficientAddress_alignment base (n-1) hj halign hbound
  apply fqDegreeProbe_none_zero next post base (BitVec.ofNat 64 (n-1))
    (coefficients (n-1)) hc ha' hi'
  · simpa only [coefficientAddress_source] using haj
  · simpa only [coefficientAddress_source] using hbj
  · simpa only [coefficientAddress_source, next, setVarHOLFinite] using hd (n-1) hj
  · simpa only [coefficientAddress_source, next, setVarHOLFinite] using hm (n-1) hj
  · exact hr

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
