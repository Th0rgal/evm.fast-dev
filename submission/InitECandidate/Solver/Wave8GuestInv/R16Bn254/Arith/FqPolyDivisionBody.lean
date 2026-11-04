import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionTail

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
open InitECandidate.Solver.PanRunBounded

/-- A complete actual division iteration derives the quotient relation from
fq_mul rather than assuming it, including both scoped local restorations. -/
theorem polyDivBody_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (A B Q : Nat → Limbs256) (inverse : Limbs256)
    (h0 : d0 < 13) (h1 : d1 < 13) (hle : d1 ≤ d0)
    (hc : state.code = originalRuntimeCode) (hl : PolyDivLocals state.locals a b quotient d0 d1)
    (hInvLocal : state.locals.lookup (ofString "linv") = some inverse.toValue)
    (hInvCanon : inverse.toNat < fqModulus.toNat)
    (hA : CanonicalPolynomial A) (hB : CanonicalPolynomial B) (hQ : CanonicalPolynomial Q)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainPolynomial state.memaddrs quotient)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hmQ : MemoryPolynomial state.memory quotient Q)
    (hAB : PolynomialDisjoint a b) (hAQ : PolynomialDisjoint a quotient)
    (hQB : PolynomialDisjoint quotient b)
    (halign : a.toNat % 8 = 0) (hbound : a.toNat + 416 ≤ 2^64)
    (hdegree : PolynomialDegreeBelow A (d0+1))
    (hinv : Nat.ModEq fqModulus.toNat ((B d1).toNat*inverse.toNat) (2^256*2^256))
    (hr : evaluateHOLFiniteState state polyDivBody = (none,post)) :
    ∃ cf : Limbs256, cf.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2^256*cf.toNat) ((A d0).toNat*inverse.toNat) ∧
      PolyDivisionStep state.memory post.memory post.locals a b quotient d0 d1 B Q cf := by
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
  have hstep := polyDivTail_none resumed inner a b quotient d0 d1 A B Q cf inverse.toNat
    h0 h1 hle (hcode.trans hc) hlR hcfR hcf hA hB hQ
    (by rw [hdomainR]; exact hdA) (by rw [hdomainR]; exact hdB) (by rw [hdomainR]; exact hdQ)
    (by rw [hmemR]; exact hmA) (by rw [hmemR]; exact hmB) (by rw [hmemR]; exact hmQ)
    hAB hAQ hQB halign hbound hdegree hinv hprod htail
  have hfinalMem : post.memory = inner.memory := by
    rw [hrestore]
    exact hpostMem
  have hfinalLocal : post.locals.lookup (ofString "d0") = inner.locals.lookup (ofString "d0") := by
    rw [hrestore]
    change (HolFiniteMapExact.resVarEq postTop.locals (ofString "top",state.locals.lookup (ofString "top"))).lookup
      (ofString "d0") = _
    simp [PanRunBounded.resVarEq_lookup,hpostLocals,show ofString "d0" ≠ ofString "top" by decide,
      show ofString "d0" ≠ ofString "cf" by decide]
  rcases hstep with ⟨C,degree,hC,hmemC,hmemB,hmemQ,hcanonQ,hval,hdegreeLocal,hrank,hframe⟩
  refine ⟨cf,hcf,hprod,C,degree,hC,?_,?_,?_,hcanonQ,hval,?_,hrank,?_⟩
  · rw [hfinalMem]; exact hmemC
  · rw [hfinalMem]; exact hmemB
  · rw [hfinalMem]; exact hmemQ
  · rw [hfinalLocal]; exact hdegreeLocal
  · intro x hxa hxq
    rw [hfinalMem,hframe x hxa hxq,hmemR]

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
