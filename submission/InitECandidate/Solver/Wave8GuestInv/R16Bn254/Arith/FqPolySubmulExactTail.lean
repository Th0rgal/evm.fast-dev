import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulSource
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqSubExactCalls

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

/-- Exact successful execution of the actual subtraction/store/increment tail. -/
theorem polySubmulTail_exact_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a shift i : BitVec 64) (A product : Limbs256)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word shift)))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word i)))
    (hA : state.locals.lookup (ofString "ai") = some A.toValue)
    (hP : state.locals.lookup (ofString "p") = some product.toValue)
    (hd : DomainU256 state.memaddrs (a+(shift+i)*32))
    (hr : evaluateHOLFiniteState state polySubmulTail = (none,post)) :
    post.memory = writeU256 state.memory (a+(shift+i)*32) (modSub256 A product fqModulus) := by
  let out := modSub256 A product fqModulus
  unfold polySubmulTail at hr
  obtain ⟨subtracted,hsub,htail⟩ := arith_seq_none hr
  obtain ⟨hlocals,hmem⟩ := fqSub_call_exact_local_none (ofString "ai")
    [polySubmulVar "ai",polySubmulVar "p"] A product hc
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,polySubmulVar,hA,hP]) hsub
  have hmeta := evaluateHOLFiniteState_metadata state
    (.call (some (some (.local,ofString "ai"),none)) (ofString "fq_sub")
      [polySubmulVar "ai",polySubmulVar "p"])
  rw [hsub] at hmeta
  have ha' : subtracted.locals.lookup (ofString "a") = some (.val (.word a)) := by
    rw [hlocals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "ai" ≠ ofString "a" by decide] using ha
  have hs' : subtracted.locals.lookup (ofString "s") = some (.val (.word shift)) := by
    rw [hlocals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "ai" ≠ ofString "s" by decide] using hs
  have hi' : subtracted.locals.lookup (ofString "i") = some (.val (.word i)) := by
    rw [hlocals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "ai" ≠ ofString "i" by decide] using hi
  have hout : arithEval subtracted (polySubmulVar "ai") = some out.toValue := by
    simp [out,arithEval,polySubmulVar,evalHOLExact,hlocals,HolFiniteMapExact.lookup_update,FUPDATE]
  have hd' : DomainU256 subtracted.memaddrs (a+(shift+i)*32) := by
    rw [hmeta.2.1]; exact hd
  have hstore := eval_store_u256 subtracted polySubmulDst (polySubmulVar "ai")
    (a+(shift+i)*32) out (polySubmul_dst_eval subtracted a shift i ha' hs' hi') hout hd'
  change evaluateHOLFiniteState subtracted polySubmulStore = _ at hstore
  rw [evaluateHOLFiniteState_seq_line780,hstore] at htail
  dsimp only at htail
  rw [polySubmul_increment {subtracted with memory := writeU256 subtracted.memory (a+(shift+i)*32) out} i hi'] at htail
  have he := congrArg (fun pair => pair.2.memory) htail
  change writeU256 subtracted.memory (a+(shift+i)*32) out = post.memory at he
  rw [hmem] at he
  exact he.symm

end InitECandidate.Solver.Wave8GuestInv.Arith
