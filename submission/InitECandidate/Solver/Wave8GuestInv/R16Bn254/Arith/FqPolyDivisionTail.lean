import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolynomialFrame

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

/-- Result of one canonical inner division step. The quotient coefficient is
updated, the dividend's rank decreases, and all other buffers are framed. -/
def PolyDivisionStep (before after : BitVec 64 → HolWordLab 64)
    (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (a b quotient : BitVec 64) (d0 d1 : Nat) (B Q : Nat → Limbs256) (cf : Limbs256) : Prop :=
  ∃ (C : Nat → Limbs256) (degree : BitVec 64),
    CanonicalPolynomial C ∧ MemoryPolynomial after a C ∧ MemoryPolynomial after b B ∧
    MemoryPolynomial after quotient (fun j => if j = d0-d1 then cf else Q j) ∧
    CanonicalPolynomial (fun j => if j = d0-d1 then cf else Q j) ∧
    PolynomialDegreeValue C (.val (.word degree)) ∧
    locals.lookup (ofString "d0") = some (.val (.word degree)) ∧
    polynomialDegreeRank degree < polynomialDegreeRank (BitVec.ofNat 64 d0) ∧
    ∀ x, PolynomialOutside a x → PolynomialOutside quotient x → after x = before x

theorem polyDivTail_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (A B Q : Nat → Limbs256) (cf : Limbs256) (inverse : Nat)
    (h0 : d0 < 13) (h1 : d1 < 13) (hle : d1 ≤ d0)
    (hc : state.code = originalRuntimeCode) (hl : PolyDivLocals state.locals a b quotient d0 d1)
    (hcf : state.locals.lookup (ofString "cf") = some cf.toValue)
    (hcfCanon : cf.toNat < fqModulus.toNat)
    (hA : CanonicalPolynomial A) (hB : CanonicalPolynomial B) (hQ : CanonicalPolynomial Q)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainPolynomial state.memaddrs quotient)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hmQ : MemoryPolynomial state.memory quotient Q)
    (hAB : PolynomialDisjoint a b) (hAQ : PolynomialDisjoint a quotient)
    (hQB : PolynomialDisjoint quotient b)
    (halign : a.toNat % 8 = 0) (hbound : a.toNat + 416 ≤ 2^64)
    (hdegree : PolynomialDegreeBelow A (d0+1))
    (hinv : Nat.ModEq fqModulus.toNat ((B d1).toNat*inverse) (2^256*2^256))
    (hprod : Nat.ModEq fqModulus.toNat (2^256*cf.toNat) ((A d0).toNat*inverse))
    (hr : evaluateHOLFiniteState state polyDivTail = (none,post)) :
    PolyDivisionStep state.memory post.memory post.locals a b quotient d0 d1 B Q cf := by
  have hshift : d0-d1 < 13 := by omega
  have hsum : d0-d1+d1 = d0 := Nat.sub_add_cancel hle
  let stored : PanSemStateFiniteExact 64 F :=
    { state with memory := writeU256 state.memory (coefficientAddress quotient (d0-d1)) cf }
  have hstore := eval_store_u256 state polyDivQAddress (polyDivVar "cf")
    (coefficientAddress quotient (d0-d1)) cf (polyDiv_q_eval state a b quotient d0 d1 hl h1 hle)
    (by simpa [arithEval,polyDivVar,evalHOLExact] using hcf) (hdQ _ hshift)
  change evaluateHOLFiniteState state polyDivStore = (none,stored) at hstore
  rw [polyDivTail,evaluateHOLFiniteState_seq_line780,hstore] at hr
  dsimp only at hr
  obtain ⟨mid,hsub,hscan⟩ := arith_seq_none hr
  have hmidlocals : mid.locals = stored.locals := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,he⟩ := arith_call_discard_none_state hsub
    rw [he]
  have hmA' : MemoryPolynomial stored.memory a A :=
    writeCoefficient_disjoint state.memory quotient a A (d0-d1) cf hshift
      (polynomialDisjoint_symm a quotient hAQ) hmA
  have hmB' : MemoryPolynomial stored.memory b B :=
    writeCoefficient_disjoint state.memory quotient b B (d0-d1) cf hshift hQB hmB
  have hmQ' : MemoryPolynomial stored.memory quotient (fun j => if j = d0-d1 then cf else Q j) :=
    writeCoefficient_polynomial state.memory quotient Q (d0-d1) cf hshift hmQ
  have hsubArgs := polyDiv_sub_args stored a b quotient d0 d1 cf hl h1 hle hcf
  have hscanArgs : evalListHOLFinite mid (h := fun x => Classical.propDecidable (mid.memaddrs x)) polyDivScanArgs =
      some [.val (.word a),.val (.word 13)] := by
    have hr0 : mid.locals.lookup (ofString "r0") = some (.val (.word a)) := by
      rw [hmidlocals]; exact hl.r0
    simp [polyDivScanArgs,polyDivVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,hr0]
  obtain ⟨C,degree,hC,hmemC,hmemB,hval,hfinalLocals,hsigned,hrank,hdegreeBound,hframe⟩ :=
    polySubmul_scan_progress stored mid post a b (d0-d1) d1 A B cf inverse (ofString "d0")
      polyDivSubArgs polyDivScanArgs h1 (by omega) hc hA hB hdA hdB hmA' hmB' hAB halign hbound
      (by simpa only [hsum] using hdegree) hinv (by simpa only [hsum] using hprod)
      hsubArgs hsub hscanArgs hscan
  refine ⟨C,degree,hC,hmemC,hmemB,
    polynomialFrame_preserves stored.memory post.memory a quotient _ hframe hAQ hmQ',
    canonicalPolynomial_update Q (d0-d1) cf hQ hcfCanon,hval,?_,?_,?_⟩
  · simp [hfinalLocals,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa only [hsum] using hrank
  · intro x hxa hxq
    rw [hframe x hxa]
    exact writeU256_frame state.memory _ x cf (hxq _ hshift)

end InitECandidate.Solver.Wave8GuestInv.Arith
