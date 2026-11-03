import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulZeroCalls

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

theorem polynomialDegreeValue_of_top (A : Nat → Limbs256) (d : Nat) (v : ValueHOL 64)
    (hd : d < 13) (hnz : (A d).toNat ≠ 0) (habove : PolynomialDegreeBelow A (d+1))
    (hv : PolynomialDegreeValue A v) : v = .val (.word (BitVec.ofNat 64 d)) := by
  rcases hv with ⟨_,hz⟩ | ⟨j,hj,rfl,hjnz,hzero⟩
  · exact False.elim (hnz (hz d hd))
  · have he : j = d := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hnz (hzero d hlt hd)
      · exact hjnz (habove j hj (by omega))
    rw [he]

theorem locals_update_same (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (name : MlS) (v : ValueHOL 64) (hv : locals.lookup name = some v) :
    locals.update (name,v) = locals := by
  apply HolFiniteMapExact.ext
  funext key
  by_cases he : key = name
  · subst key; simp [HolFiniteMapExact.lookup_update,FUPDATE,hv]
  · simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm he]

/-- Once the quotient slot already holds zero, the actual store/submul/scan
suffix preserves both memory and all caller locals. Other fields are separate. -/
theorem polyDivTail_zero_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (A B : Nat → Limbs256) (cf : Limbs256)
    (h0 : d0 < 13) (h1 : d1 < 13) (hle : d1 ≤ d0)
    (hc : state.code = originalRuntimeCode) (hl : PolyDivLocals state.locals a b quotient d0 d1)
    (hcf : state.locals.lookup (ofString "cf") = some cf.toValue) (hz : cf.toNat = 0)
    (hB : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainU256 state.memaddrs (coefficientAddress quotient (d0-d1)))
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hmQ : MemoryU256 state.memory (coefficientAddress quotient (d0-d1)) cf)
    (halign : a.toNat % 8 = 0) (hbound : a.toNat + 416 ≤ 2^64)
    (hnz : (A d0).toNat ≠ 0) (habove : PolynomialDegreeBelow A (d0+1))
    (hr : evaluateHOLFiniteState state polyDivTail = (none,post)) :
    post.memory = state.memory ∧ post.locals = state.locals := by
  have hstore := eval_store_u256 state polyDivQAddress (polyDivVar "cf")
    (coefficientAddress quotient (d0-d1)) cf (polyDiv_q_eval state a b quotient d0 d1 hl h1 hle)
    (by simpa [arithEval,polyDivVar,evalHOLExact] using hcf) hdQ
  rw [writeU256_same state.memory _ cf hmQ] at hstore
  change evaluateHOLFiniteState state polyDivStore = (none,state) at hstore
  rw [polyDivTail,evaluateHOLFiniteState_seq_line780,hstore] at hr
  dsimp only at hr
  obtain ⟨mid,hsub,hscan⟩ := arith_seq_none hr
  have hmidlocals : mid.locals = state.locals := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,he⟩ := arith_call_discard_none_state hsub
    rw [he]
  have hmidmem := polySubmul_zero_call_none state mid a b (d0-d1) d1 A B cf h1
    (by omega) hc hz hB hdA hdB hmA hmB polyDivSubArgs
    (polyDiv_sub_args state a b quotient d0 d1 cf hl h1 hle hcf) hsub
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state polyDivSubCall
  rw [hsub] at hmeta
  have hscanArgs : evalListHOLFinite mid (h := fun x => Classical.propDecidable (mid.memaddrs x)) polyDivScanArgs =
      some [.val (.word a),.val (.word 13)] := by
    have hr0 : mid.locals.lookup (ofString "r0") = some (.val (.word a)) := by
      rw [hmidlocals]; exact hl.r0
    simp [polyDivScanArgs,polyDivVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,hr0]
  obtain ⟨value,hvalue,hlocals,hmem⟩ := fqDegree_call_none_correct mid post a A (ofString "d0")
    polyDivScanArgs (hmeta.1.trans hc) halign hbound
    (by rw [hmeta.2.1]; exact hdA) (by rw [hmidmem]; exact hmA) hscanArgs hscan
  have hv := polynomialDegreeValue_of_top A d0 value h0 hnz habove hvalue
  refine ⟨hmem.trans hmidmem,?_⟩
  rw [hlocals,hmidlocals,hv]
  exact locals_update_same state.locals _ _ hl.degree0

end InitECandidate.Solver.Wave8GuestInv.Arith
