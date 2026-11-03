import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyCofactorPrepared

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

def polySwap : ProgHOL 64 :=
  .dec (ofString "t") .one (polyDivVar "r0")
    (.seq (.assign .local (ofString "r0") (polyDivVar "r1"))
    (.seq (.assign .local (ofString "r1") (polyDivVar "t"))
    (.seq (.assign .local (ofString "t") (polyDivVar "s0"))
    (.seq (.assign .local (ofString "s0") (polyDivVar "s1"))
    (.seq (.assign .local (ofString "s1") (polyDivVar "tmp"))
      (.assign .local (ofString "tmp") (polyDivVar "t")))))))

theorem polySwap_source_eq : polyCofactorFinish = polySwap := rfl

def polySwapState {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b c d e : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let inner := setVarHOLFinite (ofString "tmp") (.val (.word c))
    (setVarHOLFinite (ofString "s1") (.val (.word e))
    (setVarHOLFinite (ofString "s0") (.val (.word d))
    (setVarHOLFinite (ofString "t") (.val (.word c))
    (setVarHOLFinite (ofString "r1") (.val (.word a))
    (setVarHOLFinite (ofString "r0") (.val (.word b))
    (setVarHOLFinite (ofString "t") (.val (.word a)) s))))))
  { inner with locals := HolFiniteMapExact.resVarEq inner.locals (ofString "t",s.locals.lookup (ofString "t")) }

/-- Exact successful execution of all six actual assignments, including
restoration of the temporary t. No memory or clock field changes. -/
theorem polySwap_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (a b c d e : BitVec 64)
    (ha : s.locals.lookup (ofString "r0") = some (.val (.word a)))
    (hb : s.locals.lookup (ofString "r1") = some (.val (.word b)))
    (hc : s.locals.lookup (ofString "s0") = some (.val (.word c)))
    (hd : s.locals.lookup (ofString "s1") = some (.val (.word d)))
    (he : s.locals.lookup (ofString "tmp") = some (.val (.word e))) :
    evaluateHOLFiniteState s polySwap = (none,polySwapState s a b c d e) := by
  rw [polySwap,evaluateHOLFiniteState_dec_total]
  simp [polySwapState,evaluateHOLFiniteState_seq_line780,
    evaluateHOLFiniteState_assign,polyDivVar,evalHOLExact,ha,hb,hc,hd,he,
    shapeOfHOLExact,shapeEqHOL,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,
    setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "t" ≠ ofString "r0" by decide,
    show ofString "t" ≠ ofString "r1" by decide,
    show ofString "t" ≠ ofString "s0" by decide,
    show ofString "t" ≠ ofString "s1" by decide,
    show ofString "t" ≠ ofString "tmp" by decide,
    show ofString "r0" ≠ ofString "t" by decide,
    show ofString "r0" ≠ ofString "r1" by decide,
    show ofString "r0" ≠ ofString "s0" by decide,
    show ofString "r0" ≠ ofString "s1" by decide,
    show ofString "r0" ≠ ofString "tmp" by decide,
    show ofString "r1" ≠ ofString "t" by decide,
    show ofString "r1" ≠ ofString "s0" by decide,
    show ofString "r1" ≠ ofString "s1" by decide,
    show ofString "r1" ≠ ofString "tmp" by decide,
    show ofString "s0" ≠ ofString "t" by decide,
    show ofString "s0" ≠ ofString "s1" by decide,
    show ofString "s0" ≠ ofString "tmp" by decide,
    show ofString "s1" ≠ ofString "t" by decide,
    show ofString "s1" ≠ ofString "tmp" by decide]

theorem polySwapState_locals {F : Type} (s : PanSemStateFiniteExact 64 F) (a b c d e : BitVec 64) :
    (polySwapState s a b c d e).locals.lookup (ofString "r0") = some (.val (.word b)) ∧
    (polySwapState s a b c d e).locals.lookup (ofString "r1") = some (.val (.word a)) ∧
    (polySwapState s a b c d e).locals.lookup (ofString "s0") = some (.val (.word d)) ∧
    (polySwapState s a b c d e).locals.lookup (ofString "s1") = some (.val (.word e)) ∧
    (polySwapState s a b c d e).locals.lookup (ofString "tmp") = some (.val (.word c)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [polySwapState,setVarHOLFinite,PanRunBounded.resVarEq_lookup,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "r0" ≠ ofString "t" by decide,
      show ofString "tmp" ≠ ofString "r0" by decide,
      show ofString "s1" ≠ ofString "r0" by decide,
      show ofString "s0" ≠ ofString "r0" by decide,
      show ofString "t" ≠ ofString "r0" by decide,
      show ofString "r1" ≠ ofString "r0" by decide]
  · simp [polySwapState,setVarHOLFinite,PanRunBounded.resVarEq_lookup,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "r1" ≠ ofString "t" by decide,
      show ofString "tmp" ≠ ofString "r1" by decide,
      show ofString "s1" ≠ ofString "r1" by decide,
      show ofString "s0" ≠ ofString "r1" by decide,
      show ofString "t" ≠ ofString "r1" by decide]
  · simp [polySwapState,setVarHOLFinite,PanRunBounded.resVarEq_lookup,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "s0" ≠ ofString "t" by decide,
      show ofString "tmp" ≠ ofString "s0" by decide,
      show ofString "s1" ≠ ofString "s0" by decide]
  · simp [polySwapState,setVarHOLFinite,PanRunBounded.resVarEq_lookup,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "s1" ≠ ofString "t" by decide,
      show ofString "tmp" ≠ ofString "s1" by decide]
  · simp [polySwapState,setVarHOLFinite,PanRunBounded.resVarEq_lookup,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "tmp" ≠ ofString "t" by decide]

theorem polySwapState_keeps {F : Type} (s : PanSemStateFiniteExact 64 F) (a b c d e : BitVec 64)
    (name : MlS) (hn : name ∉ [ofString "r0",ofString "r1",ofString "s0",ofString "s1",ofString "tmp"]) :
    (polySwapState s a b c d e).locals.lookup name = s.locals.lookup name := by
  by_cases ht : name = ofString "t"
  · subst name
    simp [polySwapState,PanRunBounded.resVarEq_lookup]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    simp [polySwapState,setVarHOLFinite,PanRunBounded.resVarEq_lookup,HolFiniteMapExact.lookup_update,FUPDATE,
      ht,Ne.symm ht,Ne.symm hn.1,Ne.symm hn.2.1,Ne.symm hn.2.2.1,Ne.symm hn.2.2.2.1,Ne.symm hn.2.2.2.2]

theorem polySwap_none {F : Type} (s post : PanSemStateFiniteExact 64 F) (a b c d e : BitVec 64)
    (ha : s.locals.lookup (ofString "r0") = some (.val (.word a)))
    (hb : s.locals.lookup (ofString "r1") = some (.val (.word b)))
    (hc : s.locals.lookup (ofString "s0") = some (.val (.word c)))
    (hd : s.locals.lookup (ofString "s1") = some (.val (.word d)))
    (he : s.locals.lookup (ofString "tmp") = some (.val (.word e)))
    (hr : evaluateHOLFiniteState s polySwap = (none,post)) :
    post = polySwapState s a b c d e := by
  rw [polySwap_eval s a b c d e ha hb hc hd he] at hr
  exact (Prod.mk.inj hr).2.symm

end InitECandidate.Solver.Wave8GuestInv.Arith
