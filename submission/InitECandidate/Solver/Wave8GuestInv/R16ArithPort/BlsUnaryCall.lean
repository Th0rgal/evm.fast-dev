import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsCallFacts
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsHalfSemantics

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

def blsUnaryCall (fname dest : MlS) : ProgHOL 64 :=
  .call (some (some (.local, dest), none)) fname [.var .local dest]

/-- Typed unary calls preserve any proved relation between their argument and result. -/
theorem blsUnaryCall_typed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname dest : MlS) (body : ProgHOL 64) (a : Limbs384) (R : Limbs384 → Prop)
    (hc : s.code = originalRuntimeCode) (ha : s.locals.lookup dest = some a.toValue)
    (hi : originalRuntimeCode.lookup fname = some ([(ofString "x", blsU384Shape)], body, blsU384Shape))
    (hbody : ∀ st : PanSemStateFiniteExact 64 F, st.code = originalRuntimeCode →
      st.locals.lookup (ofString "x") = some a.toValue →
      (evaluateHOLFiniteState st body).1 = some .timeOut ∨
        ∃ r : Limbs384, R r ∧ (evaluateHOLFiniteState st body).1 = some (.returned r.toValue)) :
    (evaluateHOLFiniteState s (blsUnaryCall fname dest)).1 = some .timeOut ∨
      ∃ r : Limbs384, R r ∧
        (evaluateHOLFiniteState s (blsUnaryCall fname dest)).1 = none ∧
        (evaluateHOLFiniteState s (blsUnaryCall fname dest)).2.locals = s.locals.update (dest, r.toValue) := by
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local dest] = some [a.toValue] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha]
  let locals := HolFiniteMapExact.empty.update (ofString "x", a.toValue)
  have hlookup : lookupCodeHOLFinite s.code.lookup fname [a.toValue] =
      some (body, locals, blsU384Shape) := by
    apply arith_one_arg_lookup s.code.lookup fname (ofString "x") blsU384Shape blsU384Shape body a.toValue
    · simp [blsU384Shape, Limbs384.toValue, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · rw [hc]
      exact hi
  unfold blsUnaryCall
  rw [evaluateHOLFiniteState_call, hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  by_cases hz : s.clock = 0
  · left
    simp [hz]
  · rw [if_neg hz]
    have ht := hbody (callEntryStateHOLFinite s locals) hc
      (by simp [locals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s locals) body with ⟨res, post⟩
    rw [hrun] at ht
    rcases ht with ht | ⟨r, hR, hr⟩
    · dsimp only at ht
      subst res
      exact Or.inl rfl
    · dsimp only at hr
      subst res
      right
      refine ⟨r, hR, ?_, ?_⟩
      all_goals simp [blsU384Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL,
        Limbs384.toValue, isValidValueHOLExact, lookupKvarHOLExact, ha,
        setKvarHOLFinite, setVarHOLFinite]

theorem blsHalf_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (a : Limbs384) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup counter = some a.toValue) :
    (evaluateHOLFiniteState s (blsUnaryCall (ofString "bls_fp_shr1") counter)).1 = some .timeOut ∨
      ((evaluateHOLFiniteState s (blsUnaryCall (ofString "bls_fp_shr1") counter)).1 = none ∧
        (evaluateHOLFiniteState s (blsUnaryCall (ofString "bls_fp_shr1") counter)).2.locals =
          s.locals.update (counter, (half384 a).toValue)) := by
  have h := blsUnaryCall_typed s (ofString "bls_fp_shr1") counter
    (arithSourceBody Guest.Software.guestFn_bls_fp_shr1) a (fun r => r = half384 a) hc ha
    arith_lookup_bls_fp_shr1 (by
      intro st _ hlookup
      exact Or.inr ⟨half384 a, rfl, congrArg Prod.fst (eval_bls_fp_shr1_body st a hlookup)⟩)
  rcases h with ht | ⟨r, rfl, hn, hl⟩
  · exact Or.inl ht
  · exact Or.inr ⟨hn, hl⟩
end InitECandidate.Solver.Wave8GuestInv.Arith
