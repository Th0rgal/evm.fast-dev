import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ReturnedFacts
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.CounterUp

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

def fqDegreeProbe : ProgHOL 64 :=
  .decCall (ofString "z") .one (ofString "is_zero_bytes")
    [.op .add [.var .local (ofString "a"),
      .panop .mul [.var .local (ofString "i"), .const 32]], .const 32]
    (.ite (.cmp .equal (.var .local (ofString "z")) (.const 0))
      (.return (.var .local (ofString "i"))) .skip)

def fqDegreeDecrement : ProgHOL 64 :=
  .assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1])

def fqDegreeBody : ProgHOL 64 := .seq fqDegreeDecrement fqDegreeProbe

def fqDegreeLoop : ProgHOL 64 :=
  .while (.cmp .lower (.const 0) (.var .local (ofString "i"))) fqDegreeBody

theorem fqDegree_source_eq : arithSourceBody Guest.Software.guestFn_fq_poly_deg =
    .dec (ofString "i") .one (.var .local (ofString "n"))
      (.seq fqDegreeLoop (.return (.op .sub [.const 0, .const 1]))) := rfl

theorem fqDegree_decrement {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w))) :
    evaluateHOLFiniteState s fqDegreeDecrement =
      (none, setVarHOLFinite (ofString "i") (.val (.word (w - 1))) s) := by
  simp [fqDegreeDecrement, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
    hi, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]

/-- Every successful return from the probe is its caller's current index. -/
theorem fqDegreeProbe_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (w : BitVec 64) (hi : s.locals.lookup (ofString "i") = some (.val (.word w)))
    {ret : ValueHOL 64} (hr : evaluateHOLFiniteState s fqDegreeProbe = (some (.returned ret), post)) :
    ret = .val (.word w) := by
  unfold fqDegreeProbe at hr
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, hclock, hrun, hshape, hlocals, hcode, hcont, hpost⟩ := arith_decCall_returned hr
  have hir : resumed.locals.lookup (ofString "i") = some (.val (.word w)) := by
    rw [hlocals]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "z" ≠ ofString "i" by decide] using hi
  rw [evaluateHOLFiniteState_ite] at hcont
  split at hcont
  · split at hcont
    · simp [evaluateHOLFiniteState_skip] at hcont
    · change evaluateHOLFiniteState resumed (.return (.var .local (ofString "i"))) = _ at hcont
      rw [evaluateHOLFiniteState_return] at hcont
      simpa [evalHOLExact, hir,
        shapeOfHOLExact, sizeOfShapeWithContextHOL] using (Prod.mk.inj hcont).1.symm
  · simp at hcont

theorem fqDegreeProbe_flow_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (hi : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hf : (evaluateHOLFiniteState s fqDegreeProbe).1 = none ∨
      (evaluateHOLFiniteState s fqDegreeProbe).1 = some .continue) :
    (evaluateHOLFiniteState s fqDegreeProbe).2.locals.lookup (ofString "i") = some (.val (.word w)) := by
  have h := evaluate_avoidsLocal_flowing (ofString "i") fqDegreeProbe (by decide) s
    (hf.elim Or.inl (fun h => Or.inr (Or.inr h)))
  exact h.trans hi

theorem fqDegreeBody_returned {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (w : BitVec 64) (hi : s.locals.lookup (ofString "i") = some (.val (.word w)))
    {ret : ValueHOL 64} (hr : evaluateHOLFiniteState s fqDegreeBody = (some (.returned ret), post)) :
    ret = .val (.word (w - 1)) := by
  unfold fqDegreeBody at hr
  rw [evaluateHOLFiniteState_seq_line780, fqDegree_decrement s w hi] at hr
  exact fqDegreeProbe_returned (w - 1)
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hr

theorem fqDegreeBody_flow_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
    (w : BitVec 64) (hi : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hf : (evaluateHOLFiniteState s fqDegreeBody).1 = none ∨
      (evaluateHOLFiniteState s fqDegreeBody).1 = some .continue) :
    (evaluateHOLFiniteState s fqDegreeBody).2.locals.lookup (ofString "i") = some (.val (.word (w - 1))) := by
  unfold fqDegreeBody at hf ⊢
  rw [evaluateHOLFiniteState_seq_line780, fqDegree_decrement s w hi] at hf ⊢
  exact fqDegreeProbe_flow_lookup _ (w - 1)
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hf

end InitECandidate.Solver.Wave8GuestInv.Arith
