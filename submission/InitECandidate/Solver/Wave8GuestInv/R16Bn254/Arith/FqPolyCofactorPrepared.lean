import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyCofactorLoop

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

def polyCofactorFinish : ProgHOL 64 := polyDivSourceAt polyDivAfterLoop [true,false,true]
def polyCofactorRun (cont : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "j") .one (.const 0) (.seq polyCofactorLoop cont)

theorem polyCofactorRun_source_eq : polyDivSourceAt polyDivAfterLoop [true] =
    polyCofactorRun polyCofactorFinish := rfl

/-- The actual scoped thirteen-step update passes a canonical cofactor to
its continuation, retaining the buffer and degree locals used by the swap. -/
theorem polyCofactorRun_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (t b q : BitVec 64) (T B Q : Nat → Limbs256) (cont : ProgHOL 64)
    (hc : state.code = originalRuntimeCode)
    (ht : state.locals.lookup (ofString "tmp") = some (.val (.word t)))
    (hb : state.locals.lookup (ofString "s1") = some (.val (.word b)))
    (hq : state.locals.lookup (ofString "q") = some (.val (.word q)))
    (hT : CanonicalPolynomial T) (hB : CanonicalPolynomial B)
    (hdT : DomainPolynomial state.memaddrs t) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainPolynomial state.memaddrs q)
    (hmT : MemoryPolynomial state.memory t T) (hmB : MemoryPolynomial state.memory b B)
    (hmQ : MemoryPolynomial state.memory q Q)
    (hTB : PolynomialDisjoint t b) (hTQ : PolynomialDisjoint t q)
    (hr : evaluateHOLFiniteState state (polyCofactorRun cont) = (none,post)) :
    ∃ (C : Nat → Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      CanonicalPolynomial C ∧ MemoryPolynomial resumed.memory t C ∧
      MemoryPolynomial resumed.memory b B ∧ MemoryPolynomial resumed.memory q Q ∧
      PolynomialFrame state.memory resumed.memory t ∧ resumed.code = state.code ∧
      (∀ name, name ∈ [ofString "r0",ofString "r1",ofString "s0",ofString "s1",ofString "tmp",ofString "q",ofString "d0",ofString "d1"] →
        resumed.locals.lookup name = state.locals.lookup name) ∧
      evaluateHOLFiniteState resumed cont = (none,inner) ∧ post.memory = inner.memory ∧
      ∀ name, name ≠ ofString "j" → post.locals.lookup name = inner.locals.lookup name := by
  unfold polyCofactorRun at hr
  obtain ⟨value,inner,hinit,hshape,hseq,hrestore⟩ := arith_dec_none_state hr
  have hv : value = .val (.word 0) := by
    simpa [evalHOLFinite,evalHOLExact] using hinit.symm
  subst value
  let declared := setVarHOLFinite (ofString "j") (.val (.word 0)) state
  have hl : PolyCofactorLocals declared.locals t b q 0 := by
    constructor
    · simpa [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "j" ≠ ofString "tmp" by decide] using ht
    · simpa [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "j" ≠ ofString "s1" by decide] using hb
    · simpa [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "j" ≠ ofString "q" by decide] using hq
    · simp [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨resumed,hloop,hcont⟩ := arith_seq_none hseq
  obtain ⟨C,hC,hmC,hmB',hmQ',hframe,hindex⟩ := polyCofactorLoop_none declared resumed t b q 0 T B Q
    (by decide) hc hl hT hB hdT hdB hdQ hmT hmB hmQ hTB hTQ hloop
  have hmeta := evaluateHOLFiniteState_metadata declared polyCofactorLoop
  rw [hloop] at hmeta
  refine ⟨C,resumed,inner,hC,hmC,hmB',hmQ',hframe,hmeta.1,?_,hcont,?_,?_⟩
  · intro name hn
    have hne : ofString "j" ≠ name := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hkeep := polyCofactorLoop_keeps declared resumed name hn hloop
    simpa [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hne] using hkeep
  · rw [hrestore]
  · intro name hn
    rw [hrestore]
    change (HolFiniteMapExact.resVarEq inner.locals (ofString "j",state.locals.lookup (ofString "j"))).lookup name = _
    simp [PanRunBounded.resVarEq_lookup,hn]

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
