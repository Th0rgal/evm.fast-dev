import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulDegree
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.StateTraceNone

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

theorem arith_call_discard_none_state {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {fn : MlS} {args : List (ExpHOL 64)}
    (h : evaluateHOLFiniteState s (.call (some (none, none)) fn args) = (none, post)) :
    ∃ (vals : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (rs : ShapeHOL) (w : ValueHOL 64) (bpost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals ∧
      lookupCodeHOLFinite s.code.lookup fn vals = some (body, callee, rs) ∧
      s.clock ≠ 0 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w), bpost) ∧
      shapeEqHOL (shapeOfHOLExact w) rs = true ∧
      post = { bpost with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call] at h
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; simp at h
  | some vals =>
    rw [hargs] at h; dsimp only at h
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => rw [hlk] at h; simp at h
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      rw [hlk] at h; dsimp only at h
      split at h
      · simp at h
      · rename_i hclk
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).1
        cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rw [hrun] at h hmeta
          dsimp only at hmeta
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first | (simp [emptyLocalsHOLFinite] at h; done) | skip
          dsimp only at h
          split at h
          · rename_i hrs
            exact ⟨vals, body, callee, rs, w, bpost, rfl, hlk, hclk, hrun, hrs, (Prod.mk.inj h).2.symm⟩
          · simp at h


def polySubmulLocals (a b : BitVec 64) (q : Limbs256) (shift db : Nat) :
    HolFiniteMapExact MlS (ValueHOL 64) :=
  (((((HolFiniteMapExact.empty.update (ofString "a", .val (.word a))).update
    (ofString "b", .val (.word b))).update (ofString "q", q.toValue)).update
    (ofString "s", .val (.word (BitVec.ofNat 64 shift)))).update
    (ofString "db", .val (.word (BitVec.ofNat 64 db))))

theorem arith_lookup_fq_poly_submul :
    originalRuntimeCode.lookup (ofString "fq_poly_submul") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "q", arithU256Shape),
        (ofString "s", .one), (ofString "db", .one)],
        arithSourceBody Guest.Software.guestFn_fq_poly_submul, .one) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 681 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_fq_poly_submul) rfl

set_option maxRecDepth 1000 in
theorem polySubmul_lookup (a b : BitVec 64) (q : Limbs256) (shift db : Nat) :
    lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "fq_poly_submul")
      [.val (.word a), .val (.word b), q.toValue,
        .val (.word (BitVec.ofNat 64 shift)), .val (.word (BitVec.ofNat 64 db))] =
      some (arithSourceBody Guest.Software.guestFn_fq_poly_submul,
        polySubmulLocals a b q shift db, .one) := by
  have raw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "fq_poly_submul")
      [.val (.word a), .val (.word b), q.toValue,
        .val (.word (BitVec.ofNat 64 shift)), .val (.word (BitVec.ofNat 64 db))] =
      some (arithSourceBody Guest.Software.guestFn_fq_poly_submul,
        (polySubmulLocals a b q shift db).lookup, .one) := by
    simp [lookupCodeHOLExact, arith_lookup_fq_poly_submul, polySubmulLocals,
      Limbs256.toValue, arithU256Shape, shapeOfHOLExact, shapeEqHOL,
      HolFiniteMapExact.update, HolFiniteMapExact.empty,
      shapeEqHOL.shapeEqListHOL,
      show ofString "a" ≠ ofString "b" by decide,
      show ofString "a" ≠ ofString "q" by decide,
      show ofString "a" ≠ ofString "s" by decide,
      show ofString "a" ≠ ofString "db" by decide,
      show ofString "b" ≠ ofString "q" by decide,
      show ofString "b" ≠ ofString "s" by decide,
      show ofString "b" ≠ ofString "db" by decide,
      show ofString "q" ≠ ofString "s" by decide,
      show ofString "q" ≠ ofString "db" by decide,
      show ofString "s" ≠ ofString "db" by decide]
    funext key
    simp only [FUPDATE]
    by_cases hd : key = ofString "db"
    · subst key; simp
    have hd' := Ne.symm hd
    by_cases hs : key = ofString "s"
    · subst key; simp [hd, hd']
    have hs' := Ne.symm hs
    by_cases hq : key = ofString "q"
    · subst key; simp [hd, hs, hd', hs']
    have hq' := Ne.symm hq
    by_cases hb : key = ofString "b"
    · subst key; simp [hd, hs, hq, hd', hs', hq']
    have hb' := Ne.symm hb
    by_cases ha : key = ofString "a"
    · subst key; simp [hd, hs, hq, hb, hd', hs', hq', hb']
    have ha' := Ne.symm ha
    simp [FUPDATE, hd, hs, hq, hb, ha, hd', hs', hq', hb', ha']
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i body locals rs found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun ls => some (arithSourceBody Guest.Software.guestFn_fq_poly_submul, ls, ShapeHOL.one))
    apply HolFiniteMapExact.ext
    rfl

theorem polySubmul_callee_correct {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hdbBound : db < 13) (htarget : shift+db < 13)
    (hc : state.code = originalRuntimeCode)
    (hACanon : CanonicalPolynomial A) (hBCanon : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b)
    (ret : ValueHOL 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hlk : lookupCodeHOLFinite state.code.lookup (ofString "fq_poly_submul")
      [.val (.word a), .val (.word b), q.toValue,
        .val (.word (BitVec.ofNat 64 shift)), .val (.word (BitVec.ofNat 64 db))] =
      some (body, callee, rs))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned ret),post)) :
    ∃ C : Nat → Limbs256, CanonicalPolynomial C ∧
      MemoryPolynomial post.memory a C ∧ MemoryPolynomial post.memory b B ∧
      SubmulRange q shift 0 db A B C ∧ PolynomialFrame state.memory post.memory a := by
  rw [hc, polySubmul_lookup] at hlk
  obtain ⟨rfl,rfl,rfl⟩ := Option.some.inj hlk
  obtain ⟨C,hret,hC,hmemC,hmemB,hrange,hframe⟩ := polySubmul_returned_correct
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
    hACanon hBCanon hdA hdB hmA hmB hsep hr
  exact ⟨C,hC,hmemC,hmemB,hrange,hframe⟩

theorem polySubmul_call_none_correct {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hdbBound : db < 13) (htarget : shift+db < 13)
    (hc : state.code = originalRuntimeCode)
    (hACanon : CanonicalPolynomial A) (hBCanon : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b)
    (args : List (ExpHOL 64))
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args =
      some [.val (.word a), .val (.word b), q.toValue,
        .val (.word (BitVec.ofNat 64 shift)), .val (.word (BitVec.ofNat 64 db))])
    (hr : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "fq_poly_submul") args) =
      (none,post)) :
    ∃ C : Nat → Limbs256, CanonicalPolynomial C ∧
      MemoryPolynomial post.memory a C ∧ MemoryPolynomial post.memory b B ∧
      SubmulRange q shift 0 db A B C ∧ PolynomialFrame state.memory post.memory a := by
  obtain ⟨values,body,callee,rs,ret,bpost,he,hlk,hclock,hrun,hshape,hpost⟩ :=
    arith_call_discard_none_state hr
  have hv := Option.some.inj (he.symm.trans hargs)
  subst values
  have hresult := polySubmul_callee_correct state bpost a b shift db A B q hdbBound htarget hc
    hACanon hBCanon hdA hdB hmA hmB hsep ret body callee rs hlk hrun
  simpa only [hpost] using hresult

end InitECandidate.Solver.Wave8GuestInv.Arith
