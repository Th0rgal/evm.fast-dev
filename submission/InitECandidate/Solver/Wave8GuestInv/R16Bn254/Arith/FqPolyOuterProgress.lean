import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySwap
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolynomialRank

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

/-- After the source's copy into tmp, the actual cofactor update and swap
strictly decrease the memory-based outer rank. The remainder/old-divisor
representations are protected by the cofactor memory frame. -/
theorem polyCofactorSwap_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b c d e q : BitVec 64) (A B D T Q : Nat → Limbs256) (degree : BitVec 64) (d1 : Nat)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "r0") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "r1") = some (.val (.word b)))
    (hs0 : state.locals.lookup (ofString "s0") = some (.val (.word c)))
    (hs1 : state.locals.lookup (ofString "s1") = some (.val (.word d)))
    (htmp : state.locals.lookup (ofString "tmp") = some (.val (.word e)))
    (hq : state.locals.lookup (ofString "q") = some (.val (.word q)))
    (hT : CanonicalPolynomial T) (hD : CanonicalPolynomial D)
    (hdT : DomainPolynomial state.memaddrs e) (hdD : DomainPolynomial state.memaddrs d)
    (hdQ : DomainPolynomial state.memaddrs q)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hmD : MemoryPolynomial state.memory d D) (hmT : MemoryPolynomial state.memory e T)
    (hmQ : MemoryPolynomial state.memory q Q)
    (hEA : PolynomialDisjoint e a) (hEB : PolynomialDisjoint e b)
    (hED : PolynomialDisjoint e d) (hEQ : PolynomialDisjoint e q)
    (hdegreeA : PolynomialDegreeValue A (.val (.word degree)))
    (hdegreeB : PolynomialDegreeValue B (.val (.word (BitVec.ofNat 64 d1))))
    (hd1 : d1 < 13) (hsmall : degree.toInt < (d1 : Int))
    (hr : evaluateHOLFiniteState state (polyCofactorRun polyCofactorFinish) = (none,post)) :
    ∃ C : Nat → Limbs256, CanonicalPolynomial C ∧
      MemoryPolynomial post.memory a A ∧ MemoryPolynomial post.memory b B ∧
      MemoryPolynomial post.memory d D ∧ MemoryPolynomial post.memory e C ∧
      MemoryPolynomial post.memory q Q ∧
      post.locals.lookup (ofString "r0") = some (.val (.word b)) ∧
      post.locals.lookup (ofString "r1") = some (.val (.word a)) ∧
      post.locals.lookup (ofString "s0") = some (.val (.word d)) ∧
      post.locals.lookup (ofString "s1") = some (.val (.word e)) ∧
      post.locals.lookup (ofString "tmp") = some (.val (.word c)) ∧
      polyOuterRank post < polyOuterRank state ∧ PolynomialFrame state.memory post.memory e := by
  obtain ⟨C,resumed,inner,hC,hmC,hmD',hmQ',hframe,hcode,hkeep,hswap,hfinalMem,hfinalLocals⟩ :=
    polyCofactorRun_none state post e d q T D Q polyCofactorFinish hc htmp hs1 hq hT hD
      hdT hdD hdQ hmT hmD hmQ hED hEQ hr
  rw [polySwap_source_eq] at hswap
  have hpost := polySwap_none resumed inner a b c d e
    ((hkeep (ofString "r0") (by simp)).trans ha)
    ((hkeep (ofString "r1") (by simp)).trans hb)
    ((hkeep (ofString "s0") (by simp)).trans hs0)
    ((hkeep (ofString "s1") (by simp)).trans hs1)
    ((hkeep (ofString "tmp") (by simp)).trans htmp) hswap
  have hmem : post.memory = resumed.memory := by
    rw [hfinalMem,hpost]
    rfl
  have hptrs := polySwapState_locals resumed a b c d e
  have hr0 : post.locals.lookup (ofString "r0") = some (.val (.word b)) := by
    rw [hfinalLocals _ (by decide),hpost]; exact hptrs.1
  have hr1 : post.locals.lookup (ofString "r1") = some (.val (.word a)) := by
    rw [hfinalLocals _ (by decide),hpost]; exact hptrs.2.1
  have hs0' : post.locals.lookup (ofString "s0") = some (.val (.word d)) := by
    rw [hfinalLocals _ (by decide),hpost]; exact hptrs.2.2.1
  have hs1' : post.locals.lookup (ofString "s1") = some (.val (.word e)) := by
    rw [hfinalLocals _ (by decide),hpost]; exact hptrs.2.2.2.1
  have htmp' : post.locals.lookup (ofString "tmp") = some (.val (.word c)) := by
    rw [hfinalLocals _ (by decide),hpost]; exact hptrs.2.2.2.2
  have hmA' : MemoryPolynomial post.memory a A := by
    rw [hmem]
    exact polynomialFrame_preserves state.memory resumed.memory e a A hframe hEA hmA
  have hmB' : MemoryPolynomial post.memory b B := by
    rw [hmem]
    exact polynomialFrame_preserves state.memory resumed.memory e b B hframe hEB hmB
  refine ⟨C,hC,hmA',hmB',?_,?_,?_,hr0,hr1,hs0',hs1',htmp',?_,?_⟩
  · rw [hmem]; exact hmD'
  · rw [hmem]; exact hmC
  · rw [hmem]; exact hmQ'
  · rw [polyOuterRank_represented post a A degree hr1 hmA' hdegreeA,
      polyOuterRank_represented state b B (BitVec.ofNat 64 d1) hb hmB hdegreeB]
    apply polynomialDegreeRank_lt A _ degree hdegreeA
    simpa only [degreeIndex_toInt d1 hd1] using hsmall
  · rw [hmem]; exact hframe

end InitECandidate.Solver.Wave8GuestInv.Arith
