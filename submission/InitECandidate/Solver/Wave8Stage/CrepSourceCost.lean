import InitECandidate.Solver.Wave8Stage.CrepExpressionClock
import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CrepSourceCost

open Classical Flapjack CrepExpressionClock

/-- Source-side upper bound on additional Loop ticks. Recursive terms use
the actual source states; the constant call and loop allowances cover cuts. -/
noncomputable def sourceCost {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F) : Nat :=
  match p with
  | .assign _ e | .storeGlob _ e | .shMem _ _ e => expressionCost e
  | .store a b | .store32 a b | .storeByte a b => expressionCost a + expressionCost b
  | .return es => expressionsCost es
  | .dec n e body =>
      expressionCost e +
        match evalCrepSemHOLExp s e with
        | none => 0
        | some v => sourceCost body { s with locals := s.locals.updateEq (n, v) }
  | .seq first second =>
      let post := evalCrepSemHOLProgExact s first
      have _mono := evalCrepSemHOLProgExact_clock_le s first
      sourceCost first s +
        match post.1 with
        | none => sourceCost second post.2
        | some _ => 0
  | .ite e first second =>
      expressionCost e + 1 +
        match evalCrepSemHOLExp s e with
        | some (.word w) => if w = 0 then sourceCost second s else sourceCost first s
        | _ => 0
  | .while e body =>
      expressionCost e + 2 +
        match evalCrepSemHOLExp s e with
        | some (.word w) =>
          if _run : w ≠ 0 ∧ s.clock ≠ 0 then
            let entry := decClockCrepSemHOL s
            let post := evalCrepSemHOLProgExact entry body
            have _mono := evalCrepSemHOLProgExact_clock_le entry body
            sourceCost body entry +
              if post.1 = none ∨ post.1 = some (.continue 0) then
                sourceCost (.while e body) post.2
              else 0
          else 0
        | _ => 0
  | .call ret name args =>
      expressionsCost args + 3 +
        match args.mapM (evalCrepSemHOLExp s) with
        | none => 0
        | some vs =>
          match lookupCodeFiniteHOL s.code name vs vs.length with
          | none => 0
          | some (body, locals) =>
            if _invalid : crepReturnInfoNodupError ret then 0 else
            if _zero : s.clock = 0 then 0 else
              let entry := { decClockCrepSemHOL s with locals := locals }
              let post := evalCrepSemHOLProgExact entry body
              have _mono := evalCrepSemHOLProgExact_clock_le entry body
              sourceCost body entry +
                match ret, post.1 with
                | some (_, some (tag, handler)), some (.exception exn) =>
                  if tag = exn then sourceCost handler { post.2 with locals := s.locals } else 0
                | _, _ => 0
  | _ => 0
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals simp_wf
  all_goals try dsimp only [entry, post] at *
  all_goals try simp only [decClockCrepSemHOL] at *
  all_goals first
    | exact Prod.Lex.right _ (by simp +arith)
    | exact Prod.Lex.left _ _ (by omega)
    | exact LoopSemStateFiniteExact.lexLt (by omega) (by simp +arith)


end InitECandidate.Solver.Wave8Stage.CrepSourceCost
