import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionBody

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

structure PolyDivContext (a b quotient : BitVec 64) (d1 : Nat)
    (B : Nat → Limbs256) (inverse : Limbs256) : Prop where
  positive : 0 < d1
  bound : d1 < 13
  canonical : CanonicalPolynomial B
  degree : PolynomialDegreeValue B (.val (.word (BitVec.ofNat 64 d1)))
  inverseCanonical : inverse.toNat < fqModulus.toNat
  inverseRelation : Nat.ModEq fqModulus.toNat ((B d1).toNat*inverse.toNat) (2^256*2^256)
  separateAB : PolynomialDisjoint a b
  separateAQ : PolynomialDisjoint a quotient
  separateQB : PolynomialDisjoint quotient b
  aligned : a.toNat % 8 = 0
  nonwrapping : a.toNat + 416 ≤ 2^64

structure PolyDivInvariant {F : Type} (a b quotient : BitVec 64) (d1 : Nat)
    (B : Nat → Limbs256) (inverse : Limbs256) (s : PanSemStateFiniteExact 64 F) : Prop where
  r0 : s.locals.lookup (ofString "r0") = some (.val (.word a))
  r1 : s.locals.lookup (ofString "r1") = some (.val (.word b))
  q : s.locals.lookup (ofString "q") = some (.val (.word quotient))
  degree1 : s.locals.lookup (ofString "d1") = some (.val (.word (BitVec.ofNat 64 d1)))
  linv : s.locals.lookup (ofString "linv") = some inverse.toValue
  domainA : DomainPolynomial s.memaddrs a
  domainB : DomainPolynomial s.memaddrs b
  domainQ : DomainPolynomial s.memaddrs quotient
  divisor : MemoryPolynomial s.memory b B
  dividend : ∃ (A Q : Nat → Limbs256) (degree : BitVec 64),
    CanonicalPolynomial A ∧ CanonicalPolynomial Q ∧
    MemoryPolynomial s.memory a A ∧ MemoryPolynomial s.memory quotient Q ∧
    PolynomialDegreeValue A (.val (.word degree)) ∧
    s.locals.lookup (ofString "d0") = some (.val (.word degree))

def polyDivisionRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "d0") with
  | some (.val (.word degree)) => polynomialDegreeRank degree
  | _ => 0

theorem polyDivInvariant_rank_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (inverse : Limbs256)
    (h : PolyDivInvariant a b quotient d1 B inverse s) : polyDivisionRank s ≤ 13 := by
  obtain ⟨A,Q,degree,hA,hQ,hmA,hmQ,hdegree,hlocal⟩ := h.dividend
  simpa only [polyDivisionRank,hlocal] using polynomialDegreeRank_bound A degree hdegree

/-- A successful guarded execution of the actual source body preserves the
canonical caller invariant and strictly decreases its rank. -/
theorem polyDivBody_invariant {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (inverse : Limbs256)
    (ctx : PolyDivContext a b quotient d1 B inverse)
    (hc : s.code = originalRuntimeCode) (hi : PolyDivInvariant a b quotient d1 B inverse s)
    (word : BitVec 64)
    (hguard : evalHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) polyDivGuard =
      some (.val (.word word))) (hnz : word ≠ 0)
    (hr : evaluateHOLFiniteState s polyDivBody = (none,post)) :
    polyDivisionRank post < polyDivisionRank s ∧ PolyDivInvariant a b quotient d1 B inverse post ∧
      ∀ x, PolynomialOutside a x → PolynomialOutside quotient x → post.memory x = s.memory x := by
  obtain ⟨A,Q,degree,hA,hQ,hmA,hmQ,hdegree,hlocal⟩ := hi.dividend
  obtain ⟨w,v,hw,hv,hcmp⟩ := cmp_counter_active s (ofString "d0") .notLess (polyDivVar "d1") word hguard hnz
  have hw' : w = degree := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using hw.symm.trans hlocal
  have hv' : v = BitVec.ofNat 64 d1 := by
    simpa [polyDivVar,evalHOLFinite,evalHOLExact,hi.degree1] using hv.symm
  subst w
  subst v
  have hpositive : 0 < (BitVec.ofNat 64 d1).toInt := by
    rw [degreeIndex_toInt d1 ctx.bound]
    exact_mod_cast ctx.positive
  obtain ⟨d0,db,h0,hdb,hdbpos,hle,he0,he1,hshift,hbelow⟩ :=
    polynomialDegree_guard_indices A B degree (BitVec.ofNat 64 d1) hdegree ctx.degree hpositive hcmp
  have hdbEq : db = d1 := by
    have he := congrArg BitVec.toNat he1
    simp only [BitVec.toNat_ofNat] at he
    have hd1 := ctx.bound
    omega
  subst db
  have hl : PolyDivLocals s.locals a b quotient d0 d1 :=
    ⟨hi.r0,hi.r1,hi.q,by simpa only [he0] using hlocal,hi.degree1⟩
  obtain ⟨cf,hcf,hprod,C,after,hC,hmC,hmB,hmQ',hQ',hdeg',hlocal',hrank,hframe⟩ :=
    polyDivBody_none s post a b quotient d0 d1 A B Q inverse h0 ctx.bound hle hc hl hi.linv
      ctx.inverseCanonical hA ctx.canonical hQ hi.domainA hi.domainB hi.domainQ hmA hi.divisor hmQ
      ctx.separateAB ctx.separateAQ ctx.separateQB ctx.aligned ctx.nonwrapping hbelow ctx.inverseRelation hr
  have hmeta := evaluateHOLFiniteState_metadata s polyDivBody
  rw [hr] at hmeta
  have hdom : post.memaddrs = s.memaddrs := hmeta.2.1
  refine ⟨?_,⟨?_,?_,?_,?_,?_,?_,?_,?_,hmB,?_⟩,hframe⟩
  · simpa only [polyDivisionRank,hlocal,hlocal',he0] using hrank
  · exact (polyDivBody_keeps s post (ofString "r0") (by simp) hr).trans hi.r0
  · exact (polyDivBody_keeps s post (ofString "r1") (by simp) hr).trans hi.r1
  · exact (polyDivBody_keeps s post (ofString "q") (by simp) hr).trans hi.q
  · exact (polyDivBody_keeps s post (ofString "d1") (by simp) hr).trans hi.degree1
  · exact (polyDivBody_keeps s post (ofString "linv") (by simp) hr).trans hi.linv
  · rw [hdom]; exact hi.domainA
  · rw [hdom]; exact hi.domainB
  · rw [hdom]; exact hi.domainQ
  · exact ⟨C,(fun j => if j = d0-d1 then cf else Q j),after,hC,hQ',hmC,hmQ',hdeg',hlocal'⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
