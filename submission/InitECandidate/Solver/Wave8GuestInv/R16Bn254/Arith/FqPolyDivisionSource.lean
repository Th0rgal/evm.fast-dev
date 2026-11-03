import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionProgress

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

def polyDivVar (name : String) : ExpHOL 64 := .var .local (ofString name)
def polyDivShift : ExpHOL 64 := .op .sub [polyDivVar "d0",polyDivVar "d1"]
def polyDivTopAddress : ExpHOL 64 := .op .add [polyDivVar "r0",.panop .mul [polyDivVar "d0",.const 32]]
def polyDivQAddress : ExpHOL 64 := .op .add [polyDivVar "q",.panop .mul [polyDivShift,.const 32]]
def polyDivSubArgs : List (ExpHOL 64) :=
  [polyDivVar "r0",polyDivVar "r1",polyDivVar "cf",polyDivShift,polyDivVar "d1"]
def polyDivScanArgs : List (ExpHOL 64) := [polyDivVar "r0",.const 13]
def polyDivSubCall : ProgHOL 64 := .call (some (none,none)) (ofString "fq_poly_submul") polyDivSubArgs
def polyDivScanCall : ProgHOL 64 :=
  .call (some (some (.local,ofString "d0"),none)) (ofString "fq_poly_deg") polyDivScanArgs
def polyDivStore : ProgHOL 64 := .store polyDivQAddress (polyDivVar "cf")
def polyDivTail : ProgHOL 64 := .seq polyDivStore (.seq polyDivSubCall polyDivScanCall)
def polyDivMultiply : ProgHOL 64 :=
  .decCall (ofString "cf") arithU256Shape (ofString "fq_mul")
    [polyDivVar "top",polyDivVar "linv"] polyDivTail
def polyDivBody : ProgHOL 64 :=
  .dec (ofString "top") arithU256Shape (.load arithU256Shape polyDivTopAddress) polyDivMultiply
def polyDivGuard : ExpHOL 64 := .cmp .notLess (polyDivVar "d0") (polyDivVar "d1")
def polyDivLoop : ProgHOL 64 := .while polyDivGuard polyDivBody

/-- Structural navigation only; the equality below certifies the exact source
subtree selected, independently of the hand-written proof decomposition. -/
def polyDivSourceAt : ProgHOL 64 → List Bool → ProgHOL 64
  | p, [] => p
  | .dec _ _ _ p, false::rest => polyDivSourceAt p rest
  | .decCall _ _ _ _ p, false::rest => polyDivSourceAt p rest
  | .while _ p, false::rest => polyDivSourceAt p rest
  | .seq p _, false::rest => polyDivSourceAt p rest
  | .seq _ p, true::rest => polyDivSourceAt p rest
  | _, _ => .skip

theorem polyDiv_source_eq :
    polyDivSourceAt (arithSourceBody Guest.Software.guestFn_fq12_inv)
      ([false,false,false,false,false,false,false] ++
       [true,true,true,true,true,true,true,true,true] ++
       [false,false,false,true,false,true,false,false,false]) = polyDivLoop := rfl

structure PolyDivLocals (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (a b quotient : BitVec 64) (d0 d1 : Nat) : Prop where
  r0 : locals.lookup (ofString "r0") = some (.val (.word a))
  r1 : locals.lookup (ofString "r1") = some (.val (.word b))
  q : locals.lookup (ofString "q") = some (.val (.word quotient))
  degree0 : locals.lookup (ofString "d0") = some (.val (.word (BitVec.ofNat 64 d0)))
  degree1 : locals.lookup (ofString "d1") = some (.val (.word (BitVec.ofNat 64 d1)))

theorem PolyDivLocals.update_temp {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    {a b quotient : BitVec 64} {d0 d1 : Nat} (h : PolyDivLocals locals a b quotient d0 d1)
    (name : MlS) (value : ValueHOL 64) (hn : name = ofString "top" ∨ name = ofString "cf") :
    PolyDivLocals (locals.update (name,value)) a b quotient d0 d1 := by
  rcases hn with rfl | rfl
  · constructor
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "top" ≠ ofString "r0" by decide] using h.r0
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "top" ≠ ofString "r1" by decide] using h.r1
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "top" ≠ ofString "q" by decide] using h.q
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "top" ≠ ofString "d0" by decide] using h.degree0
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "top" ≠ ofString "d1" by decide] using h.degree1
  · constructor
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cf" ≠ ofString "r0" by decide] using h.r0
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cf" ≠ ofString "r1" by decide] using h.r1
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cf" ≠ ofString "q" by decide] using h.q
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cf" ≠ ofString "d0" by decide] using h.degree0
    · simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cf" ≠ ofString "d1" by decide] using h.degree1

theorem polyDiv_top_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (hl : PolyDivLocals s.locals a b quotient d0 d1) :
    arithEval s polyDivTopAddress = some (.val (.word (coefficientAddress a d0))) := by
  rw [← coefficientAddress_source]
  simp [arithEval,polyDivTopAddress,polyDivVar,evalHOLExact,evalListHOLExact,hl.r0,hl.degree0,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]

theorem polyDiv_shift_word (d0 d1 : Nat) (h1 : d1 < 13) (hle : d1 ≤ d0) :
    BitVec.ofNat 64 d0 - BitVec.ofNat 64 d1 = BitVec.ofNat 64 (d0-d1) :=
  BitVec.ofNat_sub_ofNat_of_le d0 d1 (by omega) hle

theorem polyDiv_q_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (hl : PolyDivLocals s.locals a b quotient d0 d1)
    (h1 : d1 < 13) (hle : d1 ≤ d0) :
    arithEval s polyDivQAddress = some (.val (.word (coefficientAddress quotient (d0-d1)))) := by
  rw [← coefficientAddress_source]
  simp [arithEval,polyDivQAddress,polyDivShift,polyDivVar,evalHOLExact,evalListHOLExact,
    hl.q,hl.degree0,hl.degree1,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,polyDiv_shift_word d0 d1 h1 hle]

theorem polyDiv_sub_args {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (cf : Limbs256)
    (hl : PolyDivLocals s.locals a b quotient d0 d1) (h1 : d1 < 13) (hle : d1 ≤ d0)
    (hcf : s.locals.lookup (ofString "cf") = some cf.toValue) :
    evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) polyDivSubArgs =
      some [.val (.word a),.val (.word b),cf.toValue,
        .val (.word (BitVec.ofNat 64 (d0-d1))),.val (.word (BitVec.ofNat 64 d1))] := by
  simp [evalListHOLFinite,evalListHOLExact,polyDivSubArgs,polyDivShift,polyDivVar,evalHOLExact,
    hl.r0,hl.r1,hl.degree0,hl.degree1,hcf,wordOpHOL,wordOp,valueIsWord,valueWord,polyDiv_shift_word d0 d1 h1 hle]

theorem polyDivBody_keeps {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (name : MlS) (hn : name ∈ [ofString "r0",ofString "r1",ofString "q",ofString "d1",ofString "linv"])
    (hr : evaluateHOLFiniteState s polyDivBody = (none,post)) :
    post.locals.lookup name = s.locals.lookup name := by
  have ha : avoidsLocal name polyDivBody = true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  have h := evaluate_avoidsLocal_flowing name polyDivBody ha s (Or.inl (by rw [hr]))
  rw [hr] at h
  exact h

end InitECandidate.Solver.Wave8GuestInv.Arith
