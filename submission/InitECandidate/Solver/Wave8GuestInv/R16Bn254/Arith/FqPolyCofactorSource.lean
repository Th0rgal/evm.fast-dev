import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionPrepared
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryPureScopedFrame

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
open InitECandidate.Solver.PanRunBounded

def polyCofactorQAddress : ExpHOL 64 :=
  .op .add [polyDivVar "q",.panop .mul [polyDivVar "j",.const 32]]
def polyCofactorSubArgs : List (ExpHOL 64) :=
  [polyDivVar "tmp",polyDivVar "s1",polyDivVar "qj",polyDivVar "j",.op .sub [.const 12,polyDivVar "j"]]
def polyCofactorCall : ProgHOL 64 :=
  .call (some (none,none)) (ofString "fq_poly_submul") polyCofactorSubArgs
def polyCofactorUpdate : ProgHOL 64 :=
  .ite (.cmp .equal (polyDivVar "qz") (.const 0)) polyCofactorCall .skip
def polyCofactorIncrement : ProgHOL 64 :=
  .assign .local (ofString "j") (.op .add [polyDivVar "j",.const 1])
def polyCofactorTail : ProgHOL 64 := .seq polyCofactorUpdate polyCofactorIncrement
def polyCofactorBody : ProgHOL 64 :=
  .dec (ofString "qj") arithU256Shape (.load arithU256Shape polyCofactorQAddress)
    (.decCall (ofString "qz") .one (ofString "u256_is_zero") [polyDivVar "qj"] polyCofactorTail)
def polyCofactorLoop : ProgHOL 64 :=
  .while (.cmp .lower (polyDivVar "j") (.const 13)) polyCofactorBody

theorem polyCofactor_source_eq :
    polyDivSourceAt polyDivAfterLoop [true,false,false] = polyCofactorLoop := rfl

structure PolyCofactorLocals (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (tmp divisor quotient : BitVec 64) (j : Nat) : Prop where
  t : locals.lookup (ofString "tmp") = some (.val (.word tmp))
  b : locals.lookup (ofString "s1") = some (.val (.word divisor))
  q : locals.lookup (ofString "q") = some (.val (.word quotient))
  index : locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 j)))

theorem PolyCofactorLocals.update_temp {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    {t b q : BitVec 64} {j : Nat} (h : PolyCofactorLocals locals t b q j)
    (name : MlS) (value : ValueHOL 64) (hn : name = ofString "qj" ∨ name = ofString "qz") :
    PolyCofactorLocals (locals.update (name,value)) t b q j := by
  rcases hn with rfl | rfl
  · constructor
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "qj" ≠ ofString "tmp" by decide] using h.t
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "qj" ≠ ofString "s1" by decide] using h.b
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "qj" ≠ ofString "q" by decide] using h.q
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "qj" ≠ ofString "j" by decide] using h.index
  · constructor
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "qz" ≠ ofString "tmp" by decide] using h.t
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "qz" ≠ ofString "s1" by decide] using h.b
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "qz" ≠ ofString "q" by decide] using h.q
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "qz" ≠ ofString "j" by decide] using h.index

theorem polyCofactor_q_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (t b q : BitVec 64) (j : Nat) (hl : PolyCofactorLocals s.locals t b q j) :
    arithEval s polyCofactorQAddress = some (.val (.word (coefficientAddress q j))) := by
  rw [← coefficientAddress_source]
  simp [arithEval,polyCofactorQAddress,polyDivVar,evalHOLExact,evalListHOLExact,hl.q,hl.index,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]

theorem polyCofactor_sub_args {F : Type} (s : PanSemStateFiniteExact 64 F)
    (t b q : BitVec 64) (j : Nat) (cf : Limbs256) (hj : j < 13)
    (hl : PolyCofactorLocals s.locals t b q j)
    (hcf : s.locals.lookup (ofString "qj") = some cf.toValue) :
    evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) polyCofactorSubArgs =
      some [.val (.word t),.val (.word b),cf.toValue,
        .val (.word (BitVec.ofNat 64 j)),.val (.word (BitVec.ofNat 64 (12-j)))] := by
  have he : (12 : BitVec 64) - BitVec.ofNat 64 j = BitVec.ofNat 64 (12-j) :=
    BitVec.ofNat_sub_ofNat_of_le 12 j (by omega) (by omega)
  simp [evalListHOLFinite,evalListHOLExact,polyCofactorSubArgs,polyDivVar,evalHOLExact,
    hl.t,hl.b,hl.index,hcf,wordOpHOL,wordOp,valueIsWord,valueWord]
  exact he

theorem polyCofactorBody_counter : CounterAdd (ofString "j") 1 polyCofactorBody := by
  exact CounterAdd.dec _ _ _ _ _ (by decide)
    (CounterAdd.decCall _ _ _ _ _ _ (by decide)
      (CounterAdd.seq _ _ _ (by decide) (by decide) (CounterAdd.assign _ _)))

theorem polyCofactorBody_keeps {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (name : MlS) (hn : name ∈ [ofString "tmp",ofString "s1",ofString "q",ofString "r0",ofString "r1"])
    (hr : evaluateHOLFiniteState s polyCofactorBody = (none,post)) :
    post.locals.lookup name = s.locals.lookup name := by
  have ha : avoidsLocal name polyCofactorBody = true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  have h := evaluate_avoidsLocal_flowing name polyCofactorBody ha s (Or.inl (by rw [hr]))
  rw [hr] at h
  exact h

end InitECandidate.Solver.Wave8GuestInv.Arith
