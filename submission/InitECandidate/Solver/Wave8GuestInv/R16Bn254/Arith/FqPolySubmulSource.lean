import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqSubCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.CounterUp

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

def polySubmulVar (name : String) : ExpHOL 64 := .var .local (ofString name)
def polySubmulSrc : ExpHOL 64 :=
  .op .add [polySubmulVar "b", .panop .mul [polySubmulVar "i", .const 32]]
def polySubmulDst : ExpHOL 64 :=
  .op .add [polySubmulVar "a", .panop .mul [.op .add [polySubmulVar "s",polySubmulVar "i"], .const 32]]
def polySubmulIncrement : ProgHOL 64 :=
  .assign .local (ofString "i") (.op .add [polySubmulVar "i", .const 1])
def polySubmulStore : ProgHOL 64 := .store polySubmulDst (polySubmulVar "ai")
def polySubmulTail : ProgHOL 64 :=
  .seq (.call (some (some (.local,ofString "ai"),none)) (ofString "fq_sub")
    [polySubmulVar "ai",polySubmulVar "p"]) (.seq polySubmulStore polySubmulIncrement)
def polySubmulLoadA : ProgHOL 64 :=
  .dec (ofString "ai") arithU256Shape (.load arithU256Shape polySubmulDst) polySubmulTail
def polySubmulMultiply : ProgHOL 64 :=
  .decCall (ofString "p") arithU256Shape (ofString "fq_mul")
    [polySubmulVar "q",polySubmulVar "bi"] polySubmulLoadA
def polySubmulBody : ProgHOL 64 :=
  .dec (ofString "bi") arithU256Shape (.load arithU256Shape polySubmulSrc) polySubmulMultiply
def polySubmulLoop : ProgHOL 64 :=
  .while (.cmp .notLower (polySubmulVar "db") (polySubmulVar "i")) polySubmulBody

theorem polySubmul_source_eq : arithSourceBody Guest.Software.guestFn_fq_poly_submul =
    .dec (ofString "i") .one (.const 0) (.seq polySubmulLoop (.return (.const 0))) := rfl

theorem polySubmul_src_eval {F : Type} (state : PanSemStateFiniteExact 64 F) (b i : BitVec 64)
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word i))) :
    arithEval state polySubmulSrc = some (.val (.word (b+i*32))) := by
  simp [arithEval, polySubmulSrc, polySubmulVar, evalHOLExact, evalListHOLExact,
    hb,hi,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]

theorem polySubmul_dst_eval {F : Type} (state : PanSemStateFiniteExact 64 F) (a shift i : BitVec 64)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word shift)))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word i))) :
    arithEval state polySubmulDst = some (.val (.word (a+(shift+i)*32))) := by
  simp [arithEval, polySubmulDst, polySubmulVar, evalHOLExact, evalListHOLExact,
    ha,hs,hi,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]

theorem polySubmul_increment {F : Type} (state : PanSemStateFiniteExact 64 F) (i : BitVec 64)
    (hi : state.locals.lookup (ofString "i") = some (.val (.word i))) :
    evaluateHOLFiniteState state polySubmulIncrement =
      (none,setVarHOLFinite (ofString "i") (.val (.word (i+1))) state) := by
  simp [polySubmulIncrement, polySubmulVar, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
    hi, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]

theorem polySubmulBody_counter : CounterAdd (ofString "i") 1 polySubmulBody := by
  exact CounterAdd.dec _ _ _ _ _ (by decide)
    (CounterAdd.decCall _ _ _ _ _ _ (by decide)
      (CounterAdd.dec _ _ _ _ _ (by decide)
        (CounterAdd.seq _ _ _ (by decide) (by decide)
          (CounterAdd.seq _ _ _ (by decide) (by decide) (CounterAdd.assign _ _)))))

theorem polySubmulBody_avoids (name : MlS)
    (hn : name ∈ [ofString "a",ofString "b",ofString "q",ofString "s",ofString "db"]) :
    avoidsLocal name polySubmulBody = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
