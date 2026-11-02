import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
Source execution cost for quantitative WordToStack simulation. Raise and
ShareInst contribute one; recursive calls and loops use the actual source
states and decreasing source clock. Sequence and conditional costs follow
the selected source branch. Invalid source guards need no simulation and
are conservatively allowed to overcount. MustTerminate contributes zero
because the simulation relation excludes its non-error execution.
-/

namespace InitECandidate.Solver.Wave8Stage.WordToStackSourceCost
open Flapjack Flapjack.WordSemStateFiniteExact

noncomputable def sourceCost {width : Nat} [NeZero width] {C F : Type}
    (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width C F) : Nat :=
  match program with
  | .raise _ | .shareInst _ _ _ => 1
  | .seq first second =>
    match run : evaluate first source with
    | (result, post) =>
      have _mono := evaluate_clock first source result post run
      sourceCost first source +
        match result with
        | none => sourceCost second post
        | some _ => 0
  | .ite cmp register operand first second =>
    match getVar register source, getVarImm operand source with
    | some left, some right =>
      match wordSemWordCmp cmp left right with
      | some true => sourceCost first source
      | some false => sourceCost second source
      | none => 0
    | _, _ => 0
  | .loop names body exitNames =>
    match cut : cutState (names,.ln) source with
    | none => 0
    | some cutSource =>
      have _cutClock := cutState_clock_termdep _ _ _ cut
      match run : evaluate body cutSource with
      | (result, post) =>
        have _mono := evaluate_clock body cutSource result post run
        sourceCost body cutSource +
          if _more : wordSemContLoop result = true ∧ post.clock ≠ 0 then
            sourceCost (wordSemSTOP (.loop names body exitNames)) (decClock post)
          else 0
  | .call ret dest args handler =>
    match getVars args source with
    | none => 0
    | some xs =>
      match wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize with
      | none => 0
      | some (args1, body, ss) =>
        if _zero : source.clock = 0 then 0 else
        match ret with
        | none =>
          match handler with
          | none => sourceCost body (callEnv args1 ss (decClock source))
          | some _ => 0
        | some (values, names, continuation, _, _) =>
          match wordSemCutEnvs names source.locals with
          | none => 0
          | some envs =>
            let entry := callEnv args1 ss (pushEnv envs handler (decClock source))
            let post := (evaluate body entry).2
            have _mono := evaluate_clock_proj body entry
            sourceCost body entry +
              max
                (match (evaluate body entry).1 with
                | some (.result _ ys) =>
                  match pop : popEnv post with
                  | none => 0
                  | some popped =>
                    have _popClock := popEnv_clock _ _ pop
                    have _popDepth := popEnv_termdep _ _ pop
                    sourceCost continuation (setVars values ys popped)
                | _ => 0)
                (match handler, (evaluate body entry).1 with
                | some (handlerVar, handlerBody, _, _), some (.exception _ value) =>
                  sourceCost handlerBody (setVar handlerVar value post)
                | _, _ => 0)
  | _ => 0
termination_by (source.termdep, source.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try dsimp only [entry, post] at *
    try simp only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock,
      WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.setVar, pushEnv_clock, pushEnv_termdep,
      wordSemSTOP, true_and] at *
    omega


end InitECandidate.Solver.Wave8Stage.WordToStackSourceCost
