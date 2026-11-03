import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionCleanupTail

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
open InitECandidate.Solver.PanRunBounded

/-- A modulus-multiple top makes the actual full body clear precisely the
quotient slot and preserve every caller local, regardless of the old slot. -/
theorem polyDivBody_cleanup_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (A B : Nat → Limbs256) (inverse : Limbs256)
    (h0 : d0 < 13) (h1 : d1 < 13) (hle : d1 ≤ d0)
    (hc : state.code = originalRuntimeCode) (hl : PolyDivLocals state.locals a b quotient d0 d1)
    (hInvLocal : state.locals.lookup (ofString "linv") = some inverse.toValue)
    (hInvCanon : inverse.toNat < fqModulus.toNat)
    (hB : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainU256 state.memaddrs (coefficientAddress quotient (d0-d1)))
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hQA : PolynomialDisjoint quotient a) (hQB : PolynomialDisjoint quotient b)
    (halign : a.toNat % 8 = 0) (hbound : a.toNat + 416 ≤ 2^64)
    (hdegree : PolynomialDegreeBelow A (d0+1))
    (hnz : (A d0).toNat ≠ 0) (hmultiple : (A d0).toNat % fqModulus.toNat = 0)
    (hr : evaluateHOLFiniteState state polyDivBody = (none,post)) :
    post.memory = writeU256 state.memory (coefficientAddress quotient (d0-d1)) fqZeroLimbs ∧
      post.locals = state.locals := by
  unfold polyDivBody at hr
  obtain ⟨top,postTop,hinit,hshape,hmul,hrestore⟩ := arith_dec_none_state hr
  have hload := eval_load_u256 state polyDivTopAddress (coefficientAddress a d0) (A d0)
    (polyDiv_top_eval state a b quotient d0 d1 hl) (hdA d0 h0) (hmA d0 h0)
  have ht : top = (A d0).toValue := Option.some.inj (hinit.symm.trans hload)
  subst top
  let declared := setVarHOLFinite (ofString "top") (A d0).toValue state
  have hlD : PolyDivLocals declared.locals a b quotient d0 d1 :=
    hl.update_temp (ofString "top") (A d0).toValue (Or.inl rfl)
  have htD : declared.locals.lookup (ofString "top") = some (A d0).toValue := by
    simp [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have hiD : declared.locals.lookup (ofString "linv") = some inverse.toValue := by
    simpa [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "top" ≠ ofString "linv" by decide] using hInvLocal
  obtain ⟨cf,resumed,inner,hcf,hprod,hlocals,hcode,hmem,hdomain,htail,hpostLocals,hpostMem⟩ :=
    fqMul_decCall_none_frame (s := declared) (post := postTop) (ofString "cf")
      [polyDivVar "top",polyDivVar "linv"] polyDivTail (A d0) inverse hc hInvCanon
      (by simp [polyDivVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,htD,hiD]) hmul
  have hlR : PolyDivLocals resumed.locals a b quotient d0 d1 := by
    rw [hlocals]
    exact hlD.update_temp (ofString "cf") cf.toValue (Or.inr rfl)
  have hcfR : resumed.locals.lookup (ofString "cf") = some cf.toValue := by
    simp [hlocals,HolFiniteMapExact.lookup_update,FUPDATE]
  have hmemR : resumed.memory = state.memory := hmem
  have hdomainR : resumed.memaddrs = state.memaddrs := hdomain
  have hcfzero : cf.toNat = 0 :=
    fqMultiple_product_zero (A d0).toNat inverse.toNat cf.toNat hmultiple hcf hprod
  have hcfeq : cf = fqZeroLimbs := limbs256_eq_zero cf hcfzero
  have hstep := polyDivTail_cleanup_none resumed inner a b quotient d0 d1 A B cf
    h0 h1 hle (hcode.trans hc) hlR hcfR hcfzero hB
    (by rw [hdomainR]; exact hdA) (by rw [hdomainR]; exact hdB) (by rw [hdomainR]; exact hdQ)
    (by rw [hmemR]; exact hmA) (by rw [hmemR]; exact hmB)
    hQA hQB halign hbound hnz hdegree htail
  refine ⟨?_,?_⟩
  · rw [hrestore]
    change postTop.memory = _
    rw [hpostMem,hstep.1,hmemR,hcfeq]
  · rw [hrestore]
    change HolFiniteMapExact.resVarEq postTop.locals
      (ofString "top",state.locals.lookup (ofString "top")) = state.locals
    rw [hpostLocals,hstep.2,hlocals]
    apply HolFiniteMapExact.ext
    funext key
    by_cases ht : key = ofString "top"
    · subst key
      simp [PanRunBounded.resVarEq_lookup]
    · by_cases hf : key = ofString "cf"
      · subst key
        simp [PanRunBounded.resVarEq_lookup,declared,setVarHOLFinite,
          HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cf" ≠ ofString "top" by decide,
          show ofString "top" ≠ ofString "cf" by decide]
      · simp [PanRunBounded.resVarEq_lookup,declared,setVarHOLFinite,
          HolFiniteMapExact.lookup_update,FUPDATE,ht,hf,Ne.symm ht,Ne.symm hf]

end InitECandidate.Solver.Wave8GuestInv.Arith
