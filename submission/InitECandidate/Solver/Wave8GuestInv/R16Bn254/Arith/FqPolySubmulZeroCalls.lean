import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulZeroCorrect
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulCalls

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

theorem polySubmul_zero_callee_correct {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hdbBound : db < 13) (htarget : shift+db < 13)
    (hc : state.code = originalRuntimeCode)
    (hqzero : q.toNat = 0) (hBCanon : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (ret : ValueHOL 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hlk : lookupCodeHOLFinite state.code.lookup (ofString "fq_poly_submul")
      [.val (.word a), .val (.word b), q.toValue,
        .val (.word (BitVec.ofNat 64 shift)), .val (.word (BitVec.ofNat 64 db))] =
      some (body, callee, rs))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned ret),post)) :
    post.memory = state.memory := by
  rw [hc, polySubmul_lookup] at hlk
  obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj hlk
  obtain ⟨hret,hmem⟩ := polySubmul_zero_returned
    (callEntryStateHOLFinite state (polySubmulLocals a b q shift db)) post a b shift db A B q ret
    hdbBound htarget hc
    (by simp [callEntryStateHOLFinite,polySubmulLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "db" ≠ ofString "a" by decide,
      show ofString "s" ≠ ofString "a" by decide,
      show ofString "q" ≠ ofString "a" by decide,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite,polySubmulLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "db" ≠ ofString "b" by decide,
      show ofString "s" ≠ ofString "b" by decide,
      show ofString "q" ≠ ofString "b" by decide])
    (by simp [callEntryStateHOLFinite,polySubmulLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "db" ≠ ofString "s" by decide])
    (by simp [callEntryStateHOLFinite,polySubmulLocals,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,polySubmulLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "db" ≠ ofString "q" by decide,
      show ofString "s" ≠ ofString "q" by decide])
    hqzero hBCanon hdA hdB hmA hmB hr
  exact hmem

theorem polySubmul_zero_call_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hdbBound : db < 13) (htarget : shift+db < 13)
    (hc : state.code = originalRuntimeCode)
    (hqzero : q.toNat = 0) (hBCanon : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (args : List (ExpHOL 64))
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args =
      some [.val (.word a), .val (.word b), q.toValue,
        .val (.word (BitVec.ofNat 64 shift)), .val (.word (BitVec.ofNat 64 db))])
    (hr : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "fq_poly_submul") args) =
      (none,post)) :
    post.memory = state.memory := by
  obtain ⟨values,body,callee,rs,ret,bpost,he,hlk,hclock,hrun,hshape,hpost⟩ :=
    arith_call_discard_none_state hr
  have hv := Option.some.inj (he.symm.trans hargs)
  subst values
  have hresult := polySubmul_zero_callee_correct state bpost a b shift db A B q hdbBound htarget hc
    hqzero hBCanon hdA hdB hmA hmB ret body callee rs hlk hrun
  simpa only [hpost] using hresult

end InitECandidate.Solver.Wave8GuestInv.Arith
