import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeRange

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

def FqDegree13 (w : BitVec 64) : Prop := w = 0 - 1 ∨ w.toNat ≤ 12

theorem fqDegree13_signed {w : BitVec 64} (hw : FqDegree13 w) :
    -1 ≤ w.toInt ∧ w.toInt ≤ 12 := by
  rcases hw with rfl | hw
  · decide
  · have he : w.toInt = w.toNat := by
      simp [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide]
      omega
    rw [he]
    omega

theorem arith_lookup_fq_poly_deg :
    originalRuntimeCode.lookup (ofString "fq_poly_deg") =
      some ([(ofString "a", .one), (ofString "n", .one)],
        arithSourceBody Guest.Software.guestFn_fq_poly_deg, .one) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 680 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_fq_poly_deg) rfl

private theorem fqDegree13_args {F : Type} (s : PanSemStateFiniteExact 64 F)
    (buffer : MlS) (values : List (ValueHOL 64))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local buffer, .const 13] = some values) :
    ∃ address : ValueHOL 64, values = [address, .val (.word 13)] := by
  cases hl : s.locals.lookup buffer with
  | none => simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hl] at ha
  | some value =>
    refine ⟨value, ?_⟩
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hl] using ha.symm

theorem fqDegree13_decCall_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp buffer : MlS) (cont : ProgHOL 64) (hc : s.code = originalRuntimeCode)
    (hr : evaluateHOLFiniteState s (.decCall temp .one (ofString "fq_poly_deg")
      [.var .local buffer, .const 13] cont) = (none, post)) :
    ∃ (degree : BitVec 64) (resumed inner : PanSemStateFiniteExact 64 F),
      FqDegree13 degree ∧ resumed.locals = s.locals.update (temp, .val (.word degree)) ∧
      resumed.code = s.code ∧ evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp, s.locals.lookup temp) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, _, hrun, _, hlocals, hcode, hcont, hpost⟩ := arith_decCall_none hr
  obtain ⟨address, rfl⟩ := fqDegree13_args s buffer values hargs
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "fq_poly_deg") (ofString "a") (ofString "n")
    .one .one .one (arithSourceBody Guest.Software.guestFn_fq_poly_deg) address (.val (.word 13))
    (by decide) arith_lookup_fq_poly_deg hlk
  have hdegree := fqDegree13_returned_range
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", address)).update
      (ofString "n", .val (.word 13)))) bpost value
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hrun
  rcases hdegree with hz | ⟨degree, hv, hsmall⟩
  · exact ⟨0 - 1, resumed, inner, Or.inl rfl, by simpa [hz] using hlocals, hcode, hcont, hpost⟩
  · exact ⟨degree, resumed, inner, Or.inr hsmall, by simpa [hv] using hlocals, hcode, hcont, hpost⟩

theorem fqDegree13_call_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest buffer : MlS) (hc : s.code = originalRuntimeCode)
    (hr : evaluateHOLFiniteState s
      (.call (some (some (.local, dest), none)) (ofString "fq_poly_deg")
        [.var .local buffer, .const 13]) = (none, post)) :
    ∃ degree : BitVec 64, FqDegree13 degree ∧
      post.locals = s.locals.update (dest, .val (.word degree)) := by
  obtain ⟨values, body, callee, rs, value, bpost, hargs, hlk, _, hrun, _, hlocals, _⟩ := arith_call_local_none hr
  obtain ⟨address, rfl⟩ := fqDegree13_args s buffer values hargs
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "fq_poly_deg") (ofString "a") (ofString "n")
    .one .one .one (arithSourceBody Guest.Software.guestFn_fq_poly_deg) address (.val (.word 13))
    (by decide) arith_lookup_fq_poly_deg hlk
  have hdegree := fqDegree13_returned_range
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", address)).update
      (ofString "n", .val (.word 13)))) bpost value
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hrun
  rcases hdegree with hz | ⟨degree, hv, hsmall⟩
  · exact ⟨0 - 1, Or.inl rfl, by simpa [hz] using hlocals⟩
  · exact ⟨degree, Or.inr hsmall, by simpa [hv] using hlocals⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
