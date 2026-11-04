import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ArithmeticReturnCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ModularArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
attribute [local irreducible] wordAddCarryHOL addCarry256 subCarry256

theorem arith_call_local_not_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dest fn : MlS) (args : List (ExpHOL 64)) (ret : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (some (.local, dest), none)) fn args)).1 ≠
      some (.returned ret) := by
  rw [evaluateHOLFiniteState_call]
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => simp
  | some vals =>
    dsimp only
    cases hlk : lookupCodeHOLFinite s.code.lookup fn vals with
    | none => simp
    | some installed =>
      obtain ⟨body, callee, rs⟩ := installed
      dsimp only
      split
      · simp
      · cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bpost =>
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals simp only
          all_goals first | (solve | simp_all) | (split <;> first | (solve | simp_all) | (split <;> simp_all))

def modSubTail : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.var .local (ofString "lt")) (.const 1))
    (.call (some (some (.local, ofString "d"), none)) (ofString "u256_add")
      [.var .local (ofString "d"), .var .local (ofString "m")]) .skip)
    (.return (.var .local (ofString "d")))

theorem modSub_source_eq : arithSourceBody Guest.Software.guestFn_mod_sub =
    .decCall (ofString "lt") .one (ofString "u256_lt")
      [.var .local (ofString "x"), .var .local (ofString "y")]
      (.decCall (ofString "d") arithU256Shape (ofString "u256_sub")
        [.var .local (ofString "x"), .var .local (ofString "y")] modSubTail) := rfl

theorem modSubTail_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (a b m : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hlt : s.locals.lookup (ofString "lt") = some (.val (.word (if a.toNat < b.toNat then 1 else 0))))
    (hd : s.locals.lookup (ofString "d") = some (subCarry256 a b).1.toValue)
    (hm : s.locals.lookup (ofString "m") = some m.toValue)
    (hr : evaluateHOLFiniteState s modSubTail = (some (.returned ret), post)) :
    ret = (modSub256 a b m).toValue := by
  have hg : evalHOLFinite s (h := fun z => Classical.propDecidable (s.memaddrs z))
      (.cmp .equal (.var .local (ofString "lt")) (.const 1)) =
      some (.val (.word (if a.toNat < b.toNat then 1 else 0))) := by
    by_cases h : a.toNat < b.toNat <;>
      simp [evalHOLFinite, evalHOLExact, hlt, h, Compiler.Encoders.Asm.wordCmpHOL]
  dsimp only [evalHOLFinite] at hg
  unfold modSubTail at hr
  rcases arith_seq_returned hr with hfirst | ⟨mid, hfirst, hret⟩
  · rw [evaluateHOLFiniteState_ite, hg] at hfirst
    by_cases h : a.toNat < b.toNat
    · simp only [h, if_true, show (1 : BitVec 64) ≠ 0 by decide, if_false] at hfirst
      exact False.elim (arith_call_local_not_returned s _ _ _ ret (congrArg Prod.fst hfirst))
    · simp [h, evaluateHOLFiniteState_skip] at hfirst
  · rw [evaluateHOLFiniteState_ite, hg] at hfirst
    have hlocal : mid.locals.lookup (ofString "d") = some (modSub256 a b m).toValue := by
      by_cases h : a.toNat < b.toNat
      · simp only [h, if_true, show (1 : BitVec 64) ≠ 0 by decide, if_false] at hfirst
        have hl := inverse_add_call_none (ofString "d") (ofString "d") (ofString "m")
          (subCarry256 a b).1 m hc hd hm hfirst
        simp [hl, HolFiniteMapExact.lookup_update, FUPDATE, modSub256, h]
      · have heq : s = mid := by simpa [h, evaluateHOLFiniteState_skip] using (congrArg Prod.snd hfirst)
        subst mid
        simpa [modSub256, h] using hd
    rw [evaluateHOLFiniteState_return] at hret
    simp [evalHOLExact, hlocal, Limbs256.toValue, shapeOfHOLExact,
      sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL] at hret
    exact hret.1.symm

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
