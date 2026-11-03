import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionCleanupProgress
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDivisionSameHead

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

/-- Every successful actual iteration with a nonzero modulus-multiple top
either strictly decreases the machine-state rank or exactly repeats the head.
Both cases preserve represented operands and establish a zero quotient slot. -/
theorem polyDivBody_multiple_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (hQA : PolynomialDisjoint quotient a) (hQB : PolynomialDisjoint quotient b)
    (halign : a.toNat % 8 = 0) (hbound : a.toNat + 416 ≤ 2^64)
    (hdegree : PolynomialDegreeBelow A (d0+1))
    (hnz : (A d0).toNat ≠ 0) (hmultiple : (A d0).toNat % fqModulus.toNat = 0)
    (hr : evaluateHOLFiniteState state polyDivBody = (none,post)) :
    (divisionHeadRank post < divisionHeadRank state ∨ post = {state with clock := post.clock}) ∧
      MemoryPolynomial post.memory a A ∧ MemoryPolynomial post.memory b B ∧
      MemoryU256 post.memory (coefficientAddress quotient (d0-d1)) fqZeroLimbs ∧
      post.locals = state.locals := by
  by_cases hz : oldSlot.toNat = 0
  · have heq : oldSlot = fqZeroLimbs := limbs256_eq_zero oldSlot hz
    have hQ : MemoryU256 state.memory (coefficientAddress quotient (d0-d1)) fqZeroLimbs := by
      rw [← heq]; exact hSlot
    have hsame := polyDivBody_sameHead state post a b quotient d0 d1 A B inverse
      h0 h1 hle hc hl hInvLocal hInvCanon hB hdA hdB hdQ hmA hmB hQ
      halign hbound hdegree hnz hmultiple hr
    refine ⟨Or.inr hsame,?_,?_,?_,?_⟩
    · rw [hsame]; exact hmA
    · rw [hsame]; exact hmB
    · rw [hsame]; exact hQ
    · rw [hsame]
  · obtain ⟨hdrop,hA',hB',hQ',hlocals⟩ := polyDivBody_cleanup_progress state post
      a b quotient d0 d1 A B inverse oldSlot h0 h1 hle hc hl hInvLocal hInvCanon
      hB hdA hdB hdQ hmA hmB hSlot hz hQA hQB halign hbound hdegree hnz hmultiple hr
    exact ⟨Or.inl hdrop,hA',hB',hQ',hlocals⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
