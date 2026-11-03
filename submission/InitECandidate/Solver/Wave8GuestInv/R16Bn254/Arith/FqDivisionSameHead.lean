import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDivisionContext
import InitECandidate.Solver.PanTerminatingNoRepeat

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

theorem state_eq_of_arithContext {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (hcontext : arithContext t = arithContext s)
    (hmem : t.memory = s.memory) (hlocals : t.locals = s.locals) :
    t = {s with clock := t.clock} := by
  cases s
  cases t
  simp_all [arithContext]

/-- The exact equation used by revision 7 SameHead, proved without modifying
or importing a different version of this branch's pinned specification. -/
theorem polyDivBody_sameHead {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (A B : Nat → Limbs256) (inverse : Limbs256)
    (h0 : d0 < 13) (h1 : d1 < 13) (hle : d1 ≤ d0)
    (hc : state.code = originalRuntimeCode) (hl : PolyDivLocals state.locals a b quotient d0 d1)
    (hInvLocal : state.locals.lookup (ofString "linv") = some inverse.toValue)
    (hInvCanon : inverse.toNat < fqModulus.toNat)
    (hB : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainU256 state.memaddrs (coefficientAddress quotient (d0-d1)))
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hmQ : MemoryU256 state.memory (coefficientAddress quotient (d0-d1)) fqZeroLimbs)
    (halign : a.toNat % 8 = 0) (hbound : a.toNat + 416 ≤ 2^64)
    (hdegree : PolynomialDegreeBelow A (d0+1))
    (hnz : (A d0).toNat ≠ 0) (hmultiple : (A d0).toNat % fqModulus.toNat = 0)
    (hr : evaluateHOLFiniteState state polyDivBody = (none,post)) :
    post = {state with clock := post.clock} := by
  have hparts := polyDivBody_zero_none state post a b quotient d0 d1 A B inverse
    h0 h1 hle hc hl hInvLocal hInvCanon hB hdA hdB hdQ hmA hmB hmQ
    halign hbound hdegree hnz hmultiple hr
  have hcontext := polyDivBody_context state hc
  rw [hr] at hcontext
  exact state_eq_of_arithContext state post hcontext hparts.1 hparts.2

/-- An active exact-repeat iteration forces the remaining while run to time out.
This uses the permitted no-repeat clock-irrelevance theorem. -/
theorem while_sameHead_timeout {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (body : ProgHOL 64) (word : BitVec 64)
    (hcond : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition =
      some (.val (.word word))) (hword : word ≠ 0)
    (hr : evaluateHOLFiniteState (decClockHOLFinite s) body = (none,post))
    (he : post = {s with clock := post.clock}) :
    (evaluateHOLFiniteState s (.while condition body)).1 = some .timeOut := by
  by_cases hclk : s.clock = 0
  · rw [evaluateHOLFiniteState_while_fixClockRewrite,hcond]
    simp only [if_pos hword,if_pos hclk]
  · have hloop := InitECandidate.Solver.PanTerminatingNoRepeat.while_unfold_continue
      condition body s word hcond hword hclk (Or.inl (by rw [hr]))
    rw [hr] at hloop
    have hbound := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
    rw [hr] at hbound
    have hlt : post.clock < s.clock := by
      change post.clock ≤ s.clock - 1 at hbound
      omega
    have hu : s = {post with clock := s.clock} := by rw [he]
    by_contra hnt
    have hntpost : (evaluateHOLFiniteState post (.while condition body)).1 ≠ some .timeOut := by
      simpa only [hloop] using hnt
    exact InitECandidate.Solver.PanTerminatingNoRepeat.evaluate_ne_of_clock_lt
      (.while condition body) post s hu hlt hloop hntpost

end InitECandidate.Solver.Wave8GuestInv.Arith
