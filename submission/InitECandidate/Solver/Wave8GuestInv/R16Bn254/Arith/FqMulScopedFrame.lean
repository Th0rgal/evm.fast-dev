import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.StateTraceNone
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMemoryPure

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

/-- Scoped multiplication exposes its continuation's unchanged memory/domain
and the final memory after local restoration. -/
theorem fqMul_decCall_none_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (temp : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64) (A B : Limbs256)
    (hc : s.code = originalRuntimeCode) (hB : B.toNat < fqModulus.toNat)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [A.toValue,B.toValue])
    (hr : evaluateHOLFiniteState s (.decCall temp arithU256Shape (ofString "fq_mul") args cont) =
      (none,post)) :
    ∃ (out : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2^256*out.toNat) (A.toNat*B.toNat) ∧
      resumed.locals = s.locals.update (temp,out.toValue) ∧ resumed.code = s.code ∧
      resumed.memory = s.memory ∧ resumed.memaddrs = s.memaddrs ∧
      evaluateHOLFiniteState resumed cont = (none,inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (temp,s.locals.lookup temp) ∧
      post.memory = inner.memory := by
  obtain ⟨values,body,callee,rs,value,bpost,resumed,inner,
    he,hlk,hclock,hrun,hshape,hlocals,hcode,hcont,hpost,hresumed,hfinal⟩ := arith_decCall_none_state hr
  have hv : values = [A.toValue,B.toValue] := Option.some.inj (he.symm.trans hargs)
  subst values
  obtain ⟨out,hret,hbound,hprod⟩ := fqMul_callee_returned A B value hc hB hlk hrun
  have hpbody : MemoryPure body := fqMul_function_memoryPure [A.toValue,B.toValue] body callee rs
    (by simpa only [hc] using hlk)
  have hmem := hpbody (callEntryStateHOLFinite s callee) hc
  have hdomain := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body).2.1
  rw [hrun] at hmem hdomain
  refine ⟨out,resumed,inner,hbound,hprod,?_,hcode,?_,?_,hcont,hpost,?_⟩
  · simpa only [hret] using hlocals
  · rw [hresumed]; exact hmem
  · rw [hresumed]; exact hdomain
  · rw [hfinal]

end InitECandidate.Solver.Wave8GuestInv.Arith
