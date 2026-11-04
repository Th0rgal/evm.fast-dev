import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyCofactorSource

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

/-- Both branches of the actual zero-coefficient test preserve canonicality
and frame every address outside tmp. The increment does not change memory. -/
theorem polyCofactorTail_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (t b q : BitVec 64) (j : Nat) (T B : Nat → Limbs256) (cf : Limbs256) (hj : j < 13)
    (hc : state.code = originalRuntimeCode) (hl : PolyCofactorLocals state.locals t b q j)
    (hcf : state.locals.lookup (ofString "qj") = some cf.toValue)
    (hT : CanonicalPolynomial T) (hB : CanonicalPolynomial B)
    (hdT : DomainPolynomial state.memaddrs t) (hdB : DomainPolynomial state.memaddrs b)
    (hmT : MemoryPolynomial state.memory t T) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint t b)
    (hr : evaluateHOLFiniteState state polyCofactorTail = (none,post)) :
    ∃ C : Nat → Limbs256, CanonicalPolynomial C ∧ MemoryPolynomial post.memory t C ∧
      MemoryPolynomial post.memory b B ∧ PolynomialFrame state.memory post.memory t := by
  unfold polyCofactorTail at hr
  obtain ⟨mid,hupdate,hinc⟩ := arith_seq_none hr
  have hargs := polyCofactor_sub_args state t b q j cf hj hl hcf
  have hresult : ∃ C : Nat → Limbs256, CanonicalPolynomial C ∧ MemoryPolynomial mid.memory t C ∧
      MemoryPolynomial mid.memory b B ∧ PolynomialFrame state.memory mid.memory t := by
    rw [polyCofactorUpdate,evaluateHOLFiniteState_ite] at hupdate
    split at hupdate
    · split at hupdate
      · rw [evaluateHOLFiniteState_skip] at hupdate
        have he : state = mid := (Prod.mk.inj hupdate).2
        subst mid
        exact ⟨T,hT,hmT,hmB,fun _ _ => rfl⟩
      · obtain ⟨C,hC,hmC,hmB',hrange,hframe⟩ := polySubmul_call_none_correct state mid t b j (12-j) T B cf
          (by omega) (by omega) hc hT hB hdT hdB hmT hmB hsep polyCofactorSubArgs hargs hupdate
        exact ⟨C,hC,hmC,hmB',hframe⟩
    · simp at hupdate
  have hmeta := evaluateHOLFiniteState_metadata state polyCofactorUpdate
  rw [hupdate] at hmeta
  have hmem := MemoryPure.assign .local (ofString "j") (.op .add [polyDivVar "j",.const 1]) mid
    (hmeta.1.trans hc)
  change (evaluateHOLFiniteState mid polyCofactorIncrement).2.memory = mid.memory at hmem
  rw [hinc] at hmem
  obtain ⟨C,hC,hmC,hmB',hframe⟩ := hresult
  refine ⟨C,hC,?_,?_,?_⟩
  · rw [hmem]; exact hmC
  · rw [hmem]; exact hmB'
  · rw [hmem]; exact hframe

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
