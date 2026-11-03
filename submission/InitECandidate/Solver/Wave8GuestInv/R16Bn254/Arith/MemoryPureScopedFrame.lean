import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.StateTraceNone
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMemoryPure

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
open InitECandidate.Solver.PanRunBounded

/-- A successful scoped call to a memory-pure function exposes its exact
continuation state and restores only the declared local at the end. -/
theorem memoryPure_decCall_none_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (fn temp : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hf : MemoryPureFunction fn)
    (hr : evaluateHOLFiniteState s (.decCall temp shape fn args cont) = (none,post)) :
    ∃ (value : ValueHOL 64) (resumed inner : PanSemStateFiniteExact 64 F),
      resumed.locals = s.locals.update (temp,value) ∧ resumed.code = s.code ∧
      resumed.memory = s.memory ∧ resumed.memaddrs = s.memaddrs ∧
      evaluateHOLFiniteState resumed cont = (none,inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp,s.locals.lookup temp) ∧
      post.memory = inner.memory := by
  obtain ⟨values,body,callee,rs,value,bpost,resumed,inner,
    he,hlk,hclock,hrun,hshape,hlocals,hcode,hcont,hpost,hresumed,hfinal⟩ := arith_decCall_none_state hr
  have hpbody : MemoryPure body := hf values body callee rs (by simpa only [hc] using hlk)
  have hmem := hpbody (callEntryStateHOLFinite s callee) hc
  have hdomain := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).2.1
  rw [hrun] at hmem hdomain
  refine ⟨value,resumed,inner,hlocals,hcode,?_,?_,hcont,hpost,?_⟩
  · rw [hresumed]; exact hmem
  · rw [hresumed]; exact hdomain
  · rw [hfinal]

end InitECandidate.Solver.Wave8GuestInv.Arith
