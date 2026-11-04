import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMemoryPure

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

theorem arith_lookup_fq_sub :
    originalRuntimeCode.lookup (ofString "fq_sub") =
      some ([(ofString "a", arithU256Shape), (ofString "b", arithU256Shape)],
        arithSourceBody Guest.Software.guestFn_fq_sub, arithU256Shape) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 650 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_fq_sub) rfl

theorem fqSub_function_memoryPure : MemoryPureFunction (ofString "fq_sub") :=
  memoryPureFunction_of_installed _ _ _ _ arith_lookup_fq_sub fqSub_memoryPure

theorem fqSub_callee_returned {F : Type} {s bpost : PanSemStateFiniteExact 64 F}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (A B : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (hA : A.toNat < fqModulus.toNat) (hB : B.toNat < fqModulus.toNat)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "fq_sub") [A.toValue, B.toValue] =
      some (body, callee, rs))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned ret), bpost)) :
    ∃ out : Limbs256, ret = out.toValue ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (out.toNat + B.toNat) A.toNat := by
  rw [hc] at hlk
  obtain ⟨_,_,rfl,rfl,_⟩ := arith_two_arg_lookup_inv_shape originalRuntimeCode.lookup
    (ofString "fq_sub") (ofString "a") (ofString "b") arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_fq_sub) A.toValue B.toValue
    (by decide) arith_lookup_fq_sub hlk
  exact fqSub_returned_canonical
    (s := callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", A.toValue)).update
      (ofString "b", B.toValue))) A B ret hc
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hA hB hr

theorem fqSub_call_local_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest : MlS) (args : List (ExpHOL 64)) (A B : Limbs256)
    (hc : s.code = originalRuntimeCode)
    (hA : A.toNat < fqModulus.toNat) (hB : B.toNat < fqModulus.toNat)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [A.toValue, B.toValue])
    (hr : evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) (ofString "fq_sub") args) =
      (none, post)) :
    ∃ out : Limbs256, out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (out.toNat + B.toNat) A.toNat ∧
      post.locals = s.locals.update (dest,out.toValue) ∧ post.memory = s.memory := by
  obtain ⟨values,body,callee,rs,value,bpost,he,hlk,hclock,hrun,hshape,hlocals,hcode⟩ := arith_call_local_none hr
  have hv : values = [A.toValue,B.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  obtain ⟨out,hret,hbound,hsub⟩ := fqSub_callee_returned A B value hc hA hB hlk hrun
  have hmem := MemoryPure.call (ofString "fq_sub") args (some (some (.local,dest)))
    fqSub_function_memoryPure s hc
  change (evaluateHOLFiniteState s (.call (some (some (.local,dest),none)) (ofString "fq_sub") args)).2.memory = s.memory at hmem
  rw [hr] at hmem
  exact ⟨out,hbound,hsub,by simpa only [hret] using hlocals,hmem⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
