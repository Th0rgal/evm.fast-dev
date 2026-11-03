import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulCorrect
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqCancellation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem submulRange_leading_zero (q : Limbs256) (inverse shift db : Nat)
    (A B C : Nat → Limbs256) (hbound : shift+db < 13)
    (hcanon : CanonicalPolynomial A) (hrange : SubmulRange q shift 0 db A B C)
    (hinv : Nat.ModEq fqModulus.toNat ((B db).toNat*inverse) (2^256*2^256))
    (hq : Nat.ModEq fqModulus.toNat (2^256*q.toNat) ((A (shift+db)).toNat*inverse)) :
    (C (shift+db)).toNat = 0 := by
  obtain ⟨product,hp,hc,hprod,hsub⟩ := hrange.2 db (by omega) (by omega)
  apply fqPoly_leading_subtract_zero (A (shift+db)).toNat (B db).toNat inverse q.toNat
    product (C (shift+db)).toNat (hcanon _ hbound) hp hc hinv hq _ hsub
  simpa only [Nat.mul_comm] using hprod

theorem submulRange_degree_decrease (q : Limbs256) (inverse shift db : Nat)
    (A B C : Nat → Limbs256) (hbound : shift+db < 13)
    (hcanon : CanonicalPolynomial A) (hrange : SubmulRange q shift 0 db A B C)
    (hdegree : PolynomialDegreeBelow A (shift+db+1))
    (hinv : Nat.ModEq fqModulus.toNat ((B db).toNat*inverse) (2^256*2^256))
    (hq : Nat.ModEq fqModulus.toNat (2^256*q.toNat) ((A (shift+db)).toNat*inverse)) :
    PolynomialDegreeBelow C (shift+db) := by
  have hz := submulRange_leading_zero q inverse shift db A B C hbound hcanon hrange hinv hq
  intro j hj hge
  by_cases he : j = shift+db
  · simpa only [he] using hz
  · rw [hrange.1 j (Or.inr (by omega))]
    exact hdegree j hj (by omega)

/-- Actual source polynomial subtraction clears the leading coefficient and
preserves the caller's canonical buffer invariant under the certified inverse
and quotient relations. This does not assume arbitrary inputs are canonical. -/
theorem polySubmul_returned_degree_decrease {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256) (inverse : Nat)
    (ret : ValueHOL 64) (hdbBound : db < 13) (htarget : shift+db < 13)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))))
    (hdb : state.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db))))
    (hqLocal : state.locals.lookup (ofString "q") = some q.toValue)
    (hACanon : CanonicalPolynomial A) (hBCanon : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b) (hdegree : PolynomialDegreeBelow A (shift+db+1))
    (hinv : Nat.ModEq fqModulus.toNat ((B db).toNat*inverse) (2^256*2^256))
    (hq : Nat.ModEq fqModulus.toNat (2^256*q.toNat) ((A (shift+db)).toNat*inverse))
    (hr : evaluateHOLFiniteState state (arithSourceBody Guest.Software.guestFn_fq_poly_submul) =
      (some (.returned ret),post)) :
    ∃ C : Nat → Limbs256, CanonicalPolynomial C ∧ MemoryPolynomial post.memory a C ∧
      MemoryPolynomial post.memory b B ∧ PolynomialDegreeBelow C (shift+db) ∧
      PolynomialFrame state.memory post.memory a := by
  obtain ⟨C,hret,hC,hmemC,hmemB,hrange,hframe⟩ := polySubmul_returned_correct state post a b shift db
    A B q ret hdbBound htarget hc ha hb hs hdb hqLocal hACanon hBCanon hdA hdB hmA hmB hsep hr
  exact ⟨C,hC,hmemC,hmemB,
    submulRange_degree_decrease q inverse shift db A B C htarget hACanon hrange hdegree hinv hq,hframe⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
