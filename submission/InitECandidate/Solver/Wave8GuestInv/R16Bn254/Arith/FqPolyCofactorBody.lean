import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyCofactorTail

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

/-- One actual cofactor iteration preserves the canonical destination, the
source cofactor and quotient buffers, and all other memory. -/
theorem polyCofactorBody_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (t b q : BitVec 64) (j : Nat) (T B Q : Nat → Limbs256) (hj : j < 13)
    (hc : state.code = originalRuntimeCode) (hl : PolyCofactorLocals state.locals t b q j)
    (hT : CanonicalPolynomial T) (hB : CanonicalPolynomial B)
    (hdT : DomainPolynomial state.memaddrs t) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainPolynomial state.memaddrs q)
    (hmT : MemoryPolynomial state.memory t T) (hmB : MemoryPolynomial state.memory b B)
    (hmQ : MemoryPolynomial state.memory q Q)
    (hTB : PolynomialDisjoint t b) (hTQ : PolynomialDisjoint t q)
    (hr : evaluateHOLFiniteState state polyCofactorBody = (none,post)) :
    ∃ C : Nat → Limbs256, CanonicalPolynomial C ∧ MemoryPolynomial post.memory t C ∧
      MemoryPolynomial post.memory b B ∧ MemoryPolynomial post.memory q Q ∧
      PolynomialFrame state.memory post.memory t := by
  unfold polyCofactorBody at hr
  obtain ⟨cf,postCF,hinit,hshape,hzero,hrestore⟩ := arith_dec_none_state hr
  have hload := eval_load_u256 state polyCofactorQAddress (coefficientAddress q j) (Q j)
    (polyCofactor_q_eval state t b q j hl) (hdQ j hj) (hmQ j hj)
  have hcf : cf = (Q j).toValue := Option.some.inj (hinit.symm.trans hload)
  subst cf
  let declared := setVarHOLFinite (ofString "qj") (Q j).toValue state
  have hlD : PolyCofactorLocals declared.locals t b q j :=
    hl.update_temp (ofString "qj") (Q j).toValue (Or.inl rfl)
  obtain ⟨value,resumed,inner,hlocals,hcode,hmem,hdomain,htail,hpostLocals,hpostMem⟩ :=
    memoryPure_decCall_none_frame (s := declared) (post := postCF) (ofString "u256_is_zero")
      (ofString "qz") .one [polyDivVar "qj"] polyCofactorTail hc u256IsZero_memoryPure hzero
  have hlR : PolyCofactorLocals resumed.locals t b q j := by
    rw [hlocals]
    exact hlD.update_temp (ofString "qz") value (Or.inr rfl)
  have hcfR : resumed.locals.lookup (ofString "qj") = some (Q j).toValue := by
    simp [hlocals,declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "qz" ≠ ofString "qj" by decide]
  have hmemR : resumed.memory = state.memory := hmem
  have hdomainR : resumed.memaddrs = state.memaddrs := hdomain
  obtain ⟨C,hC,hmC,hmB',hframe⟩ := polyCofactorTail_none resumed inner t b q j T B (Q j) hj
    (hcode.trans hc) hlR hcfR hT hB
    (by rw [hdomainR]; exact hdT) (by rw [hdomainR]; exact hdB)
    (by rw [hmemR]; exact hmT) (by rw [hmemR]; exact hmB) hTB htail
  have hfinalMem : post.memory = inner.memory := by
    rw [hrestore]; exact hpostMem
  have hframe' : PolynomialFrame state.memory post.memory t := by
    rw [hfinalMem,← hmemR]
    exact hframe
  refine ⟨C,hC,?_,?_,polynomialFrame_preserves state.memory post.memory t q Q hframe' hTQ hmQ,hframe'⟩
  · rw [hfinalMem]; exact hmC
  · rw [hfinalMem]; exact hmB'

end InitECandidate.Solver.Wave8GuestInv.Arith
