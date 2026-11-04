import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionZeroTail
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolynomialFrame

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- The zero-quotient suffix changes exactly its quotient slot. The dividend,
divisor and all caller locals are unchanged, with arbitrary old quotient data. -/
theorem polyDivTail_cleanup_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (A B : Nat → Limbs256) (cf : Limbs256)
    (h0 : d0 < 13) (h1 : d1 < 13) (hle : d1 ≤ d0)
    (hc : state.code = originalRuntimeCode) (hl : PolyDivLocals state.locals a b quotient d0 d1)
    (hcf : state.locals.lookup (ofString "cf") = some cf.toValue) (hz : cf.toNat = 0)
    (hB : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainU256 state.memaddrs (coefficientAddress quotient (d0-d1)))
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hQA : PolynomialDisjoint quotient a) (hQB : PolynomialDisjoint quotient b)
    (halign : a.toNat % 8 = 0) (hbound : a.toNat + 416 ≤ 2^64)
    (hnz : (A d0).toNat ≠ 0) (habove : PolynomialDegreeBelow A (d0+1))
    (hr : evaluateHOLFiniteState state polyDivTail = (none,post)) :
    post.memory = writeU256 state.memory (coefficientAddress quotient (d0-d1)) cf ∧
      post.locals = state.locals := by
  have hshift : d0-d1 < 13 := by omega
  let stored : PanSemStateFiniteExact 64 F :=
    {state with memory := writeU256 state.memory (coefficientAddress quotient (d0-d1)) cf}
  have hmA' : MemoryPolynomial stored.memory a A :=
    writeCoefficient_disjoint state.memory quotient a A (d0-d1) cf hshift hQA hmA
  have hmB' : MemoryPolynomial stored.memory b B :=
    writeCoefficient_disjoint state.memory quotient b B (d0-d1) cf hshift hQB hmB
  have hstore := eval_store_u256 state polyDivQAddress (polyDivVar "cf")
    (coefficientAddress quotient (d0-d1)) cf (polyDiv_q_eval state a b quotient d0 d1 hl h1 hle)
    (by simpa [arithEval,polyDivVar,evalHOLExact] using hcf) hdQ
  change evaluateHOLFiniteState state polyDivStore = (none,stored) at hstore
  rw [polyDivTail,evaluateHOLFiniteState_seq_line780,hstore] at hr
  dsimp only at hr
  obtain ⟨mid,hsub,hscan⟩ := arith_seq_none hr
  have hmidlocals : mid.locals = state.locals := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,he⟩ := arith_call_discard_none_state hsub
    rw [he]
  have hmidmem := polySubmul_zero_call_none stored mid a b (d0-d1) d1 A B cf h1
    (by omega) hc hz hB hdA hdB hmA' hmB' polyDivSubArgs
    (polyDiv_sub_args stored a b quotient d0 d1 cf hl h1 hle hcf) hsub
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata stored polyDivSubCall
  rw [hsub] at hmeta
  have hscanArgs : evalListHOLFinite mid (h := fun x => Classical.propDecidable (mid.memaddrs x)) polyDivScanArgs =
      some [.val (.word a),.val (.word 13)] := by
    have hr0 : mid.locals.lookup (ofString "r0") = some (.val (.word a)) := by
      rw [hmidlocals]; exact hl.r0
    simp [polyDivScanArgs,polyDivVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,hr0]
  obtain ⟨value,hvalue,hlocals,hmem⟩ := fqDegree_call_none_correct mid post a A (ofString "d0")
    polyDivScanArgs (hmeta.1.trans hc) halign hbound
    (by rw [hmeta.2.1]; exact hdA) (by rw [hmidmem]; exact hmA') hscanArgs hscan
  have hv := polynomialDegreeValue_of_top A d0 value h0 hnz habove hvalue
  refine ⟨hmem.trans hmidmem,?_⟩
  rw [hlocals,hmidlocals,hv]
  exact locals_update_same state.locals _ _ hl.degree0

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
