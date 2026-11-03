import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeCorrect
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeCall

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

def PolynomialDegreeValue (coefficients : Nat → Limbs256) (ret : ValueHOL 64) : Prop :=
  (ret = .val (.word (0 - 1)) ∧ ∀ j, j < 13 → (coefficients j).toNat = 0) ∨
  ∃ j : Nat, j < 13 ∧ ret = .val (.word (BitVec.ofNat 64 j)) ∧ (coefficients j).toNat ≠ 0 ∧
    ∀ k, j < k → k < 13 → (coefficients k).toNat = 0

theorem fqDegree_function_memoryPure : MemoryPureFunction (ofString "fq_poly_deg") :=
  memoryPureFunction_of_installed _ _ _ _ arith_lookup_fq_poly_deg fqDegree_memoryPure

theorem fqDegree_callee_correct {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (coefficients : Nat → Limbs256) (ret : ValueHOL 64)
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (halign : base.toNat % 8 = 0) (hbound : base.toNat + 416 ≤ 2 ^ 64)
    (hd : DomainPolynomial s.memaddrs base) (hm : MemoryPolynomial s.memory base coefficients)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "fq_poly_deg")
      [.val (.word base), .val (.word 13)] = some (body, callee, rs))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned ret), post)) : PolynomialDegreeValue coefficients ret := by
  rw [hc] at hlk
  obtain ⟨_,_,rfl,rfl,rfl⟩ := arith_two_arg_lookup_inv_shape originalRuntimeCode.lookup
    (ofString "fq_poly_deg") (ofString "a") (ofString "n") .one .one .one
    (arithSourceBody Guest.Software.guestFn_fq_poly_deg) (.val (.word base)) (.val (.word 13))
    (by decide) arith_lookup_fq_poly_deg hlk
  exact fqDegree_returned_correct (callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "a", .val (.word base))).update
      (ofString "n", .val (.word 13)))) post base coefficients 13 ret (by decide) hc
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    halign hbound hd hm hr

theorem fqDegree_call_none_correct {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (coefficients : Nat → Limbs256) (dest : MlS) (args : List (ExpHOL 64))
    (hc : s.code = originalRuntimeCode)
    (halign : base.toNat % 8 = 0) (hbound : base.toNat + 416 ≤ 2 ^ 64)
    (hd : DomainPolynomial s.memaddrs base) (hm : MemoryPolynomial s.memory base coefficients)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [.val (.word base), .val (.word 13)])
    (hr : evaluateHOLFiniteState s (.call (some (some (.local, dest), none))
      (ofString "fq_poly_deg") args) = (none, post)) :
    ∃ value : ValueHOL 64, PolynomialDegreeValue coefficients value ∧
      post.locals = s.locals.update (dest, value) ∧ post.memory = s.memory := by
  obtain ⟨values, body, callee, rs, value, bpost, heargs, hlk, hclock, hrun, hshape, hlocals, hcode⟩ :=
    arith_call_local_none hr
  have hv : values = [.val (.word base), .val (.word 13)] := Option.some.inj (heargs.symm.trans hargs)
  subst values
  have hdegree := fqDegree_callee_correct s bpost base coefficients value body callee rs hc
    halign hbound hd hm hlk hrun
  have hmem := MemoryPure.call (ofString "fq_poly_deg") args (some (some (.local,dest)))
    fqDegree_function_memoryPure s hc
  change (evaluateHOLFiniteState s (.call (some (some (.local,dest), none))
    (ofString "fq_poly_deg") args)).2.memory = s.memory at hmem
  rw [hr] at hmem
  exact ⟨value, hdegree, hlocals, hmem⟩

theorem fqDegree_decCall_none_correct {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (coefficients : Nat → Limbs256)
    (temp : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode)
    (halign : base.toNat % 8 = 0) (hbound : base.toNat + 416 ≤ 2 ^ 64)
    (hd : DomainPolynomial s.memaddrs base) (hm : MemoryPolynomial s.memory base coefficients)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [.val (.word base), .val (.word 13)])
    (hr : evaluateHOLFiniteState s (.decCall temp .one (ofString "fq_poly_deg") args cont) = (none, post)) :
    ∃ (value : ValueHOL 64) (resumed inner : PanSemStateFiniteExact 64 F),
      PolynomialDegreeValue coefficients value ∧ resumed.locals = s.locals.update (temp,value) ∧
      resumed.code = s.code ∧ evaluateHOLFiniteState resumed cont = (none,inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp,s.locals.lookup temp) := by
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    heargs, hlk, hclock, hrun, hshape, hlocals, hcode, hcont, hpost⟩ := arith_decCall_none hr
  have hv : values = [.val (.word base), .val (.word 13)] := Option.some.inj (heargs.symm.trans hargs)
  subst values
  exact ⟨value,resumed,inner,
    fqDegree_callee_correct s bpost base coefficients value body callee rs hc halign hbound hd hm hlk hrun,
    hlocals,hcode,hcont,hpost⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
