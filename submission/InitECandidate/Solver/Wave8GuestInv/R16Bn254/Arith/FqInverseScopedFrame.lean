import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.StateTraceNone
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseMemoryPure

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

/-- Scoped inversion exposes its continuation's unchanged memory/domain
and the final memory after local restoration. -/
theorem fqInverse_decCall_none_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64) (A : Limbs256)
    (hc : s.code = originalRuntimeCode) (hA : A.toNat ≠ 0)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [A.toValue])
    (hr : evaluateHOLFiniteState s (.decCall temp arithU256Shape (ofString "fq_inv") args cont) =
      (none,post)) :
    ∃ (out : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (A.toNat*out.toNat) (2^256*2^256) ∧
      resumed.locals = s.locals.update (temp,out.toValue) ∧ resumed.code = s.code ∧
      resumed.memory = s.memory ∧ resumed.memaddrs = s.memaddrs ∧
      evaluateHOLFiniteState resumed cont = (none,inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp,s.locals.lookup temp) ∧
      post.memory = inner.memory := by
  obtain ⟨values,body,callee,rs,value,bpost,resumed,inner,
    he,hlk,hclock,hrun,hshape,hlocals,hcode,hcont,hpost,hresumed,hfinal⟩ := arith_decCall_none_state hr
  have hv : values = [A.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  obtain ⟨out,hret,hbound,hprod⟩ := fqInverse_callee_returned A value hc hA hlk hrun
  have hpbody : MemoryPure body := fqInverse_function_memoryPure [A.toValue] body callee rs
    (by simpa only [hc] using hlk)
  have hmem := hpbody (callEntryStateHOLFinite s callee) hc
  have hdomain := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).2.1
  rw [hrun] at hmem hdomain
  refine ⟨out,resumed,inner,hbound,hprod,?_,hcode,?_,?_,hcont,hpost,?_⟩
  · simpa only [hret] using hlocals
  · rw [hresumed]; exact hmem
  · rw [hresumed]; exact hdomain
  · rw [hfinal]

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
