import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulCorrect
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.TailReturnedFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem arith_lookup_fq_mul :
    originalRuntimeCode.lookup (ofString "fq_mul") =
      some ([(ofString "a", arithU256Shape), (ofString "b", arithU256Shape)],
        arithSourceBody Guest.Software.guestFn_fq_mul, arithU256Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 652 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_fq_mul) rfl

/-- The installed fq_mul callee has the checked whole-source contract. -/
theorem fqMul_callee_returned {F : Type} {s bpost : PanSemStateFiniteExact 64 F}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (A B : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (hB : B.toNat < fqModulus.toNat)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "fq_mul") [A.toValue, B.toValue] =
      some (body, callee, rs))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned ret), bpost)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * out.toNat) (A.toNat * B.toNat) := by
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, _⟩ := arith_two_arg_lookup_inv_shape
    originalRuntimeCode.lookup (ofString "fq_mul") (ofString "a") (ofString "b")
    arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_fq_mul) A.toValue B.toValue
    (by decide) arith_lookup_fq_mul hlk
  exact fqMul_returned_canonical
    (s := callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", A.toValue)).update
      (ofString "b", B.toValue))) A B ret hc
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hB hr

theorem fqMul_tailCall_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (args : List (ExpHOL 64)) (A B : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hB : B.toNat < fqModulus.toNat)
    (hargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args =
      some [A.toValue, B.toValue])
    (hr : evaluateHOLFiniteState s (.call none (ofString "fq_mul") args) =
      (some (.returned ret), post)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * out.toNat) (A.toNat * B.toNat) := by
  obtain ⟨values, body, callee, rs, bpost, he, hlk, _, hrun, _⟩ := arith_tailCall_returned hr
  have hv : values = [A.toValue, B.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  exact fqMul_callee_returned A B ret hc hB hlk hrun

/-- A scoped call supplies its continuation with a canonical Montgomery product. -/
theorem fqMul_decCall_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (A B : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hB : B.toNat < fqModulus.toNat)
    (hargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args =
      some [A.toValue, B.toValue])
    (hr : evaluateHOLFiniteState s
      (.decCall temp arithU256Shape (ofString "fq_mul") args cont) = (some (.returned ret), post)) :
    ∃ (out : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * out.toNat) (A.toNat * B.toNat) ∧
      resumed.locals = s.locals.update (temp, out.toValue) ∧ resumed.code = s.code ∧
      evaluateHOLFiniteState resumed cont = (some (.returned ret), inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp, s.locals.lookup temp) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    he, hlk, _, hrun, _, hlocals, hcode, hcont, hpost⟩ := arith_decCall_returned hr
  have hv : values = [A.toValue, B.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  obtain ⟨out, hret, hbound, hprod⟩ := fqMul_callee_returned A B value hc hB hlk hrun
  exact ⟨out, resumed, inner, hbound, hprod, by simpa only [hret] using hlocals,
    hcode, hcont, hpost⟩

/-- A normal local-destination call installs the canonical product. -/
theorem fqMul_call_local_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest : MlS) (args : List (ExpHOL 64)) (A B : Limbs256)
    (hc : s.code = originalRuntimeCode) (hB : B.toNat < fqModulus.toNat)
    (hargs : evalListHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z)) args =
      some [A.toValue, B.toValue])
    (hr : evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) (ofString "fq_mul") args) =
      (none, post)) :
    ∃ out : Limbs256, out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * out.toNat) (A.toNat * B.toNat) ∧
      post.locals = s.locals.update (dest, out.toValue) := by
  obtain ⟨values, body, callee, rs, value, bpost, he, hlk, _, hrun, _, hlocals, _⟩ := arith_call_local_none hr
  have hv : values = [A.toValue, B.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  obtain ⟨out, hret, hbound, hprod⟩ := fqMul_callee_returned A B value hc hB hlk hrun
  exact ⟨out, hbound, hprod, by simpa only [hret] using hlocals⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
