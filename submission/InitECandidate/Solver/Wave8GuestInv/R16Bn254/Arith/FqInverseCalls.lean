import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInverseCorrect

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem arith_lookup_fq_inv :
    originalRuntimeCode.lookup (ofString "fq_inv") =
      some ([(ofString "a", arithU256Shape)], arithSourceBody Guest.Software.guestFn_fq_inv, arithU256Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 655 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_fq_inv) rfl

theorem fqInverse_callee_returned {F : Type} {s bpost : PanSemStateFiniteExact 64 F}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (a : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode) (ha0 : a.toNat ≠ 0)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "fq_inv") [a.toValue] = some (body, callee, rs))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned ret), bpost)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (a.toNat * out.toNat) (2 ^ 256 * 2 ^ 256) := by
  rw [hc] at hlk
  have hlookup := arith_one_arg_lookup originalRuntimeCode.lookup (ofString "fq_inv")
    (ofString "a") arithU256Shape arithU256Shape (arithSourceBody Guest.Software.guestFn_fq_inv) a.toValue
    (by simp [arithU256Shape, Limbs256.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    arith_lookup_fq_inv
  rw [hlookup] at hlk
  cases hlk
  exact fqInverse_returned_correct (s := callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "a", a.toValue))) a ret hc
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) ha0 hr

theorem fqInverse_tailCall_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (args : List (ExpHOL 64)) (a : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (ha0 : a.toNat ≠ 0)
    (hargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args = some [a.toValue])
    (hr : evaluateHOLFiniteState s (.call none (ofString "fq_inv") args) = (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (a.toNat * out.toNat) (2 ^ 256 * 2 ^ 256) := by
  obtain ⟨values, body, callee, rs, bpost, he, hlk, _, hrun, _⟩ := arith_tailCall_returned hr
  have hv : values = [a.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  exact fqInverse_callee_returned a ret hc ha0 hlk hrun

/-- A successful scoped inverse call carries its canonical inverse relation
into the continuation, without assuming memory contents beyond the argument. -/
theorem fqInverse_decCall_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64) (a : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (ha0 : a.toNat ≠ 0)
    (hargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args = some [a.toValue])
    (hr : evaluateHOLFiniteState s (.decCall temp arithU256Shape (ofString "fq_inv") args cont) =
      (some (.returned ret), post)) :
    ∃ (out : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (a.toNat * out.toNat) (2 ^ 256 * 2 ^ 256) ∧
      resumed.locals = s.locals.update (temp, out.toValue) ∧ resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (some (.returned ret), inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp, s.locals.lookup temp) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    he, hlk, _, hrun, _, hlocals, hcode, hcont, hpost⟩ := arith_decCall_returned hr
  have hv : values = [a.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  obtain ⟨out, hret, hbound, hinv⟩ := fqInverse_callee_returned a value hc ha0 hlk hrun
  exact ⟨out, resumed, inner, hbound, hinv, by simpa only [hret] using hlocals,
    hcode, hcont, hpost⟩

/-- A successful scoped inverse call carries its canonical inverse relation
into the continuation, without assuming memory contents beyond the argument. -/
theorem fqInverse_decCall_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64) (a : Limbs256)
    (hc : s.code = originalRuntimeCode) (ha0 : a.toNat ≠ 0)
    (hargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args = some [a.toValue])
    (hr : evaluateHOLFiniteState s (.decCall temp arithU256Shape (ofString "fq_inv") args cont) =
      (none, post)) :
    ∃ (out : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (a.toNat * out.toNat) (2 ^ 256 * 2 ^ 256) ∧
      resumed.locals = s.locals.update (temp, out.toValue) ∧ resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp, s.locals.lookup temp) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    he, hlk, _, hrun, _, hlocals, hcode, hcont, hpost⟩ := arith_decCall_none hr
  have hv : values = [a.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  obtain ⟨out, hret, hbound, hinv⟩ := fqInverse_callee_returned a value hc ha0 hlk hrun
  exact ⟨out, resumed, inner, hbound, hinv, by simpa only [hret] using hlocals,
    hcode, hcont, hpost⟩

theorem fqInverse_call_local_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest : MlS) (args : List (ExpHOL 64)) (a : Limbs256)
    (hc : s.code = originalRuntimeCode) (ha0 : a.toNat ≠ 0)
    (hargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args = some [a.toValue])
    (hr : evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) (ofString "fq_inv") args) =
      (none, post)) :
    ∃ out : Limbs256, out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (a.toNat * out.toNat) (2 ^ 256 * 2 ^ 256) ∧
      post.locals = s.locals.update (dest, out.toValue) := by
  obtain ⟨values, body, callee, rs, value, bpost, he, hlk, _, hrun, _, hlocals, _⟩ := arith_call_local_none hr
  have hv : values = [a.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  obtain ⟨out, hret, hbound, hinv⟩ := fqInverse_callee_returned a value hc ha0 hlk hrun
  exact ⟨out, hbound, hinv, by simpa only [hret] using hlocals⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
