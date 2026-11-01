import InitECandidate.Solver.Wave8Stage.CrepSourceCost
import Flapjack.Pancake.Semantics.CrepProps

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8Stage.CrepSourceCostBound

open Classical Flapjack CrepExpressionClock CrepSourceCost

/-- Static potential between source clock decrements. Calls pay the callee
potential from their entry tick; loops pay each body from its iteration tick. -/
def programCost {width : Nat} [NeZero width] : CrepProgHOL width → Nat
  | .assign _ e | .storeGlob _ e | .shMem _ _ e => expressionCost e
  | .store a b | .store32 a b | .storeByte a b => expressionCost a + expressionCost b
  | .return es => expressionsCost es
  | .dec _ e body => expressionCost e + programCost body
  | .seq first second => programCost first + programCost second
  | .ite e first second => expressionCost e + 1 + programCost first + programCost second
  | .while e body => expressionCost e + 2 + programCost body
  | .call ret _ args =>
      expressionsCost args + 3 +
        match ret with
        | some (_, some (_, handler)) => programCost handler
        | _ => 0
  | _ => 0
termination_by p => sizeOf p
decreasing_by all_goals simp_wf; all_goals omega

@[simp] theorem programCost_call {width : Nat} [NeZero width]
    (ret : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (name : Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width)) :
    programCost (.call ret name args) = expressionsCost args + 3 +
      (match ret with
       | some (_, some (_, handler)) => programCost handler
       | _ => 0) := by
  cases ret with
  | none => simp [programCost]
  | some ret =>
    rcases ret with ⟨names, handler⟩
    cases handler with
    | none => simp [programCost]
    | some handler => rcases handler with ⟨tag, body⟩; simp [programCost]

def codeCostBound {width : Nat} [NeZero width]
    (code : HolFiniteMapExact Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width)) (bound : Nat) : Prop :=
  ∀ name params body, code.lookup name = some (params, body) → programCost body ≤ bound

private theorem callee_bound {width : Nat} [NeZero width]
    (code : HolFiniteMapExact Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width)) (bound : Nat) (hc : codeCostBound code bound)
    (name : Basis.Pure.MlString.MlString) (args : List (HolWordLab width))
    (body : CrepProgHOL width) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (hl : lookupCodeFiniteHOL code name args args.length = some (body, locals)) :
    programCost body ≤ bound := by
  unfold lookupCodeFiniteHOL at hl
  split at hl
  · cases hl
  · split at hl
    · simp only [Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, _⟩ := hl
      exact hc _ _ _ ‹_›
    · cases hl

/-- Source cost plus remaining potential never exceeds the initial clock
potential and the current fragment's static potential. -/
theorem sourceCost_bound {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F) (bound : Nat)
    (hp : programCost p ≤ bound) (hc : codeCostBound s.code bound) :
    sourceCost p s + bound * (evalCrepSemHOLProgExact s p).2.clock ≤
      bound * s.clock + programCost p := by
  have mono := Nat.mul_le_mul_left bound (evalCrepSemHOLProgExact_clock_le s p)
  revert hp
  cases heq : p <;> intro hp
  case dec n e body =>
    simp only [programCost_call, programCost] at hp ⊢
    rw [sourceCost, evalCrepSemHOLProgExact_dec_holShape]
    cases hv : evalCrepSemHOLExp s e with
    | none => simp; omega
    | some v =>
      simp only
      have ih := sourceCost_bound body { s with locals := s.locals.updateEq (n, v) }
        bound (by omega) hc
      dsimp only at ih ⊢
      omega
  case seq first second =>
    simp only [programCost_call, programCost] at hp ⊢
    rw [sourceCost, evalCrepSemHOLProgExact_seq_holShape]
    rcases hf : evalCrepSemHOLProgExact s first with ⟨r, t⟩
    have firstClock : t.clock ≤ s.clock := by
      have h := evalCrepSemHOLProgExact_clock_le s first
      rw [hf] at h; exact h
    have hi1 := sourceCost_bound first s bound (by omega) hc
    rw [hf] at hi1
    simp only [hf]
    cases r with
    | some r => simp only [reduceCtorEq, if_false]; dsimp only at hi1 ⊢; omega
    | none =>
      simp only [ite_true]
      dsimp only at hi1 ⊢
      have hcode := evaluateCodeInvariantHOL first s none t hf
      have hi2 := sourceCost_bound second t bound (by omega) (hcode ▸ hc)
      omega
  case ite e first second =>
    simp only [programCost_call, programCost] at hp ⊢
    rw [sourceCost, evalCrepSemHOLProgExact_eq_evaluate_def]
    simp only [crepExactEvalExpClassical_eq]
    cases hv : evalCrepSemHOLExp s e with
    | none => simp; omega
    | some v =>
      cases v with
      | word w =>
        by_cases hw : w = 0
        · simp only [hw, if_true, ne_eq, not_true_eq_false, if_false]
          have hi := sourceCost_bound second s bound (by omega) hc
          omega
        · simp only [hw, if_false, ne_eq, not_false_eq_true, if_true]
          have hi := sourceCost_bound first s bound (by omega) hc
          omega
  case «while» e body =>
    have hbody : programCost body ≤ bound := by simp only [programCost] at hp; omega
    rw [sourceCost, evalCrepSemHOLProgExact_while_holShape]
    simp only [programCost_call, programCost] at hp ⊢
    cases hv : evalCrepSemHOLExp s e with
    | none => simp; omega
    | some v =>
      cases v with
      | word w =>
        by_cases hw : w = 0
        · simp [hw]; omega
        · simp only [hw, ne_eq, not_false_eq_true, if_true, true_and]
          by_cases hz : s.clock = 0
          · simp [hz, CrepSemHOLState.emptyLocals]
          · simp only [hz, not_false_eq_true, if_true, if_false, dite_true, dite_false]
            let entry := decClockCrepSemHOL s
            rcases hb : evalCrepSemHOLProgExact entry body with ⟨r, t⟩
            have hi := sourceCost_bound body entry bound hbody hc
            rw [hb] at hi
            have hmono := evalCrepSemHOLProgExact_clock_le entry body
            rw [hb] at hmono
            have strict : t.clock < s.clock := by
              dsimp only [entry, decClockCrepSemHOL] at hmono
              omega
            have hcode := evaluateCodeInvariantHOL body entry r t hb
            have step := sourceCost_bound (.while e body) t bound (by simpa only [programCost] using hp) (hcode ▸ hc)
            simp only [programCost] at step
            simp only [entry] at hb hi hmono
            simp only [dite_true, dite_false, Prod.fst, Prod.snd]
            dsimp only [entry, decClockCrepSemHOL] at hi hmono ⊢
            have hpay : bound * s.clock = bound * (s.clock - 1) + bound := by
              calc
                bound * s.clock = bound * (s.clock - 1 + 1) := congrArg (bound * ·) (by omega)
                _ = _ := by simp [Nat.mul_add]
            cases r with
            | none => simp only [true_or, if_true]; omega
            | some r =>
              cases r <;> simp only [Option.some.injEq, reduceCtorEq, false_or] <;>
                (try rename_i n) <;>
                (try cases n) <;>
                simp_all only [CrepResultHOLExact.continue.injEq, Nat.succ_ne_zero, not_false_eq_true, if_false,
                  if_true, reduceCtorEq, false_or, true_or, or_self,
                  exitLoopCrepResult, Prod.fst, Prod.snd] <;>
                omega
  case call ret name args =>
    rw [sourceCost, evalCrepSemHOLProgExact_call_holShape]
    rcases ha : args.mapM (evalCrepSemHOLExp s) with _ | vs
    · try dsimp only; try simp only [programCost_call, programCost] at hp ⊢; omega
    · simp only
      rcases hl : lookupCodeFiniteHOL s.code name vs vs.length with _ | ⟨body, locals⟩
      · try dsimp only; try simp only [programCost_call, programCost] at hp ⊢; omega
      · simp only
        by_cases hinvalid : crepReturnInfoNodupError ret
        · simp only [hinvalid, if_true, dite_true]; try simp only [programCost_call, programCost] at hp ⊢; omega
        · simp only [hinvalid, if_false, dite_false]
          by_cases hz : s.clock = 0
          · simp only [hz, if_true, dite_true, CrepSemHOLState.emptyLocals]
            try simp only [programCost_call, programCost] at hp ⊢; omega
          · simp only [hz, if_false, dite_false]
            let entry := { decClockCrepSemHOL s with locals := locals }
            rcases hb : evalCrepSemHOLProgExact entry body with ⟨r, t⟩
            have hmono := evalCrepSemHOLProgExact_clock_le entry body
            rw [hb] at hmono
            have hbody := callee_bound s.code bound hc name vs body locals hl
            have hi := sourceCost_bound body entry bound hbody hc
            rw [hb] at hi
            have strict : t.clock < s.clock := by
              dsimp only [entry, decClockCrepSemHOL] at hmono
              omega
            have hcode := evaluateCodeInvariantHOL body entry r t hb
            have hpay : bound * s.clock = bound * (s.clock - 1) + bound := by
              calc
                bound * s.clock = bound * (s.clock - 1 + 1) := congrArg (bound * ·) (by omega)
                _ = _ := by simp [Nat.mul_add]
            dsimp only [entry] at hb
            simp only [dite_true, dite_false, Prod.fst, Prod.snd]
            dsimp only [entry, decClockCrepSemHOL] at hi ⊢
            cases r with
            | none =>
              simp only [programCost_call, Nat.add_zero] at hp ⊢
              omega
            | some r =>
              cases r with
              | exception exn =>
                cases ret with
                | none => simp [programCost, CrepSemHOLState.emptyLocals] at hp ⊢; omega
                | some ret =>
                  rcases ret with ⟨rts, handler⟩
                  cases handler with
                  | none => simp [programCost, CrepSemHOLState.emptyLocals] at hp ⊢; omega
                  | some handler =>
                    rcases handler with ⟨tag, handler⟩
                    simp only [programCost_call, programCost] at hp ⊢
                    by_cases htag : tag = exn
                    · simp only [htag, if_true, ite_true]
                      have hh := sourceCost_bound handler { t with locals := s.locals }
                        bound (by omega) (hcode ▸ hc)
                      dsimp only at hh
                      omega
                    · simp only [htag, Ne.symm htag, if_false, CrepSemHOLState.emptyLocals]
                      omega
              | «return» vs =>
                cases ret with
                | none => simp [programCost, CrepSemHOLState.emptyLocals]; omega
                | some ret =>
                  rcases ret with ⟨rts, handler⟩
                  simp only [programCost_call, programCost]
                  split <;> (try split) <;> dsimp only <;> omega
              | _ =>
                try simp only [programCost_call, programCost, CrepSemHOLState.emptyLocals] at hp ⊢
                try dsimp only
                omega

  all_goals
    have he : sourceCost p s = programCost p := by
      subst p; simp only [sourceCost, programCost]
    rw [← heq] at *
    rw [he]
    omega
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals subst p
  all_goals simp_wf
  all_goals try dsimp only [entry, decClockCrepSemHOL] at *
  all_goals first
    | exact Prod.Lex.right _ (by simp +arith)
    | exact Prod.Lex.left _ _ (by omega)
    | exact LoopSemStateFiniteExact.lexLt (by omega) (by simp +arith)

#print axioms sourceCost_bound

end InitECandidate.Solver.Wave8Stage.CrepSourceCostBound
