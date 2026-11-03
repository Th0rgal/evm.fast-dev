import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionCleanupBody
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDivisionHeadRank

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

/-- Actual phase-1 cleanup strictly decreases the machine-state rank and
establishes the zero-slot representation required by the stationary case. -/
theorem polyDivBody_cleanup_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (A B : Nat → Limbs256) (inverse oldSlot : Limbs256)
    (h0 : d0 < 13) (h1 : d1 < 13) (hle : d1 ≤ d0)
    (hc : state.code = originalRuntimeCode) (hl : PolyDivLocals state.locals a b quotient d0 d1)
    (hInvLocal : state.locals.lookup (ofString "linv") = some inverse.toValue)
    (hInvCanon : inverse.toNat < fqModulus.toNat)
    (hB : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainU256 state.memaddrs (coefficientAddress quotient (d0-d1)))
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hSlot : MemoryU256 state.memory (coefficientAddress quotient (d0-d1)) oldSlot)
    (hSlotNZ : oldSlot.toNat ≠ 0)
    (hQA : PolynomialDisjoint quotient a) (hQB : PolynomialDisjoint quotient b)
    (halign : a.toNat % 8 = 0) (hbound : a.toNat + 416 ≤ 2^64)
    (hdegree : PolynomialDegreeBelow A (d0+1))
    (hnz : (A d0).toNat ≠ 0) (hmultiple : (A d0).toNat % fqModulus.toNat = 0)
    (hr : evaluateHOLFiniteState state polyDivBody = (none,post)) :
    divisionHeadRank post < divisionHeadRank state ∧
      MemoryPolynomial post.memory a A ∧ MemoryPolynomial post.memory b B ∧
      MemoryU256 post.memory (coefficientAddress quotient (d0-d1)) fqZeroLimbs ∧
      post.locals = state.locals := by
  obtain ⟨hmem,hlocals⟩ := polyDivBody_cleanup_none state post a b quotient d0 d1 A B inverse
    h0 h1 hle hc hl hInvLocal hInvCanon hB hdA hdB hdQ hmA hmB hQA hQB
    halign hbound hdegree hnz hmultiple hr
  have hshift : d0-d1 < 13 := by omega
  have hA' : MemoryPolynomial post.memory a A := by
    rw [hmem]
    exact writeCoefficient_disjoint state.memory quotient a A (d0-d1) fqZeroLimbs hshift hQA hmA
  have hB' : MemoryPolynomial post.memory b B := by
    rw [hmem]
    exact writeCoefficient_disjoint state.memory quotient b B (d0-d1) fqZeroLimbs hshift hQB hmB
  have hQ' : MemoryU256 post.memory (coefficientAddress quotient (d0-d1)) fqZeroLimbs := by
    rw [hmem]
    exact writeU256_value state.memory _ fqZeroLimbs
  have hl' : PolyDivLocals post.locals a b quotient d0 d1 := by rw [hlocals]; exact hl
  refine ⟨?_,hA',hB',hQ',hlocals⟩
  rw [divisionHeadRank_represented post a b quotient d0 d1 (A d0) fqZeroLimbs h0 h1 hl' (hA' d0 h0) hQ',
    divisionHeadRank_represented state a b quotient d0 d1 (A d0) oldSlot h0 h1 hl (hmA d0 h0) hSlot]
  exact divisionStationaryRank_cleanup_drop d0 (A d0).toNat oldSlot.toNat hmultiple hSlotNZ

end InitECandidate.Solver.Wave8GuestInv.Arith
