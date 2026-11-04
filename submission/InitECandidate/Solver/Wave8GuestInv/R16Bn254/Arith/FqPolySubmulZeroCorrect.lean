import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulZeroLoop
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulNoReturn
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.StateTraceReturned

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

/-- The actual zero-quotient submul function returns zero without changing memory. -/
theorem polySubmul_zero_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256) (ret : ValueHOL 64)
    (hdbBound : db < 13) (htarget : shift+db < 13)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))))
    (hdb : state.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db))))
    (hq : state.locals.lookup (ofString "q") = some q.toValue)
    (hqzero : q.toNat = 0) (hBCanon : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hr : evaluateHOLFiniteState state (arithSourceBody Guest.Software.guestFn_fq_poly_submul) =
      (some (.returned ret),post)) :
    ret = .val (.word 0) ∧ post.memory = state.memory := by
  rw [polySubmul_source_eq] at hr
  obtain ⟨value,inner,hinit,hshape,hbody,hrestore⟩ := arith_dec_returned_state hr
  have hv : value = .val (.word 0) := by
    simpa [evalHOLFinite,evalHOLExact] using hinit.symm
  subst value
  let entry := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have ha' : entry.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "a" by decide] using ha
  have hb' : entry.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "b" by decide] using hb
  have hs' : entry.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "s" by decide] using hs
  have hdb' : entry.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db))) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "db" by decide] using hdb
  have hq' : entry.locals.lookup (ofString "q") = some q.toValue := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "q" by decide] using hq
  rcases arith_seq_returned hbody with hloopret | ⟨mid,hloop,hreturn⟩
  · exact False.elim (polySubmulLoop_not_returned entry ret (congrArg Prod.fst hloopret))
  · have hloopmem := polySubmulLoop_zero_none entry mid a b shift 0 db A B q
      (by omega) hdbBound htarget hc ha' hb' hs'
      (by simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) hdb' hq'
      hqzero hBCanon hdA hdB hmA hmB hloop
    have hreturn' : evaluateHOLFiniteState mid (.return (.const 0)) =
        (some (.returned (.val (.word 0))),emptyLocalsHOLFinite mid) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
    rw [hreturn'] at hreturn
    have he : ret = .val (.word 0) := by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (Prod.mk.inj hreturn).1.symm
    have hmem : post.memory = mid.memory := by
      rw [hrestore,← (Prod.mk.inj hreturn).2]
      rfl
    exact ⟨he,hmem.trans hloopmem⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
