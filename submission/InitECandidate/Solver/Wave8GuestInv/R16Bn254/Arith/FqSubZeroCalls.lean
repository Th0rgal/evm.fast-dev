import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqStationaryValues
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqSubCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryU256Eval

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem fqSub_callee_zero_returned {F : Type} {s bpost : PanSemStateFiniteExact 64 F}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (A B : Limbs256) (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (hB : B.toNat = 0)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "fq_sub") [A.toValue, B.toValue] =
      some (body, callee, rs))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned ret), bpost)) :
    ret = A.toValue := by
  rw [hc] at hlk
  obtain ⟨_,_,rfl,rfl,_⟩ := arith_two_arg_lookup_inv_shape originalRuntimeCode.lookup
    (ofString "fq_sub") (ofString "a") (ofString "b") arithU256Shape arithU256Shape arithU256Shape
    (arithSourceBody Guest.Software.guestFn_fq_sub) A.toValue B.toValue
    (by decide) arith_lookup_fq_sub hlk
  exact fqSub_returned_zero_identity
    (s := callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "a", A.toValue)).update
      (ofString "b", B.toValue))) A B ret hc
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hB hr

theorem fqSub_call_zero_local_none {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (dest : MlS) (args : List (ExpHOL 64)) (A B : Limbs256)
    (hc : s.code = originalRuntimeCode)
    (hB : B.toNat = 0)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [A.toValue, B.toValue])
    (hr : evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) (ofString "fq_sub") args) =
      (none, post)) :
    post.locals = s.locals.update (dest,A.toValue) ∧ post.memory = s.memory := by
  obtain ⟨values,body,callee,rs,value,bpost,he,hlk,hclock,hrun,hshape,hlocals,hcode⟩ := arith_call_local_none hr
  have hv : values = [A.toValue,B.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  have hret := fqSub_callee_zero_returned A B value hc hB hlk hrun
  have hmem := MemoryPure.call (ofString "fq_sub") args (some (some (.local,dest)))
    fqSub_function_memoryPure s hc
  change (evaluateHOLFiniteState s (.call (some (some (.local,dest),none)) (ofString "fq_sub") args)).2.memory = s.memory at hmem
  rw [hr] at hmem
  exact ⟨by simpa only [hret] using hlocals,hmem⟩

/-- Writing an already represented value leaves the entire memory function equal. -/
theorem writeU256_same (memory : BitVec 64 → HolWordLab 64) (address : BitVec 64)
    (value : Limbs256) (hm : MemoryU256 memory address value) :
    writeU256 memory address value = memory := by
  funext x
  simp only [writeU256]
  split
  · rename_i hx; subst x; exact hm.2.2.2.symm
  · split
    · rename_i hx; subst x; exact hm.2.2.1.symm
    · split
      · rename_i hx; subst x; exact hm.2.1.symm
      · split
        · rename_i hx; subst x; exact hm.1.symm
        · rfl

end InitECandidate.Solver.Wave8GuestInv.Arith
