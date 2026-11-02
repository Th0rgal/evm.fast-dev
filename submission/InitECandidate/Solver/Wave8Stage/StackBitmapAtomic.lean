import InitECandidate.Solver.Wave8Stage.StackBitmapPrimitives
import InitECandidate.Solver.Wave8Stage.StackBitmapAccess
import InitECandidate.Solver.Wave8Stage.StackEmptyOracle

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace InitECandidate.Solver.Wave8Stage.StackBitmapAtomic
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open StackSemStateOps StackSemEvaluate StackSemExpressions StackSemShMem

/-- Atomic clauses which do not inspect the bitmap table. -/
def Ordinary {width : Nat} [NeZero width] : HolProg width → Prop
  | .alloc _ | .storeConsts _ _ _ | .bitmapLoad _ _ | .install _ _ _ _ _ |
    .seq _ _ | .ite _ _ _ _ _ | .loop _ | .call _ _ _ | .jumpLower _ _ _ | .rawCall _ => False
  | _ => True

/-- All nonrecursive clauses outside allocation and bitmap access commute
with arbitrary replacement of the bitmap table, including error results. -/
theorem ordinary_withBitmaps {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) (ordinary : Ordinary p) :
    evaluate (p,{s with bitmaps := bitmaps}) =
      Prod.map id (fun post => {post with bitmaps := bitmaps}) (evaluate (p,s)) := by
  classical
  cases p <;> simp only [Ordinary] at ordinary
  all_goals try (
    simp only [evaluate_skip, evaluate_halt, evaluate_ret, evaluate_raise,
      evaluate_break, evaluate_continue, evaluate_get, evaluate_set,
      evaluate_opCurrHeap, evaluate_tick, evaluate_codeBufferWrite,
      evaluate_dataBufferWrite, evaluate_ffi, evaluate_locValue,
      evaluate_stackAlloc, evaluate_stackFree, evaluate_stackLoad,
      evaluate_stackLoadAny, evaluate_stackStore, evaluate_stackStoreAny,
      evaluate_stackGetSize, evaluate_stackSetSize,
      StackBitmapPrimitives.wordExp_withBitmaps, getVar,
      setVar, setStore, emptyEnv, decClock, Prod.map, id_eq] <;>
    repeat' first | split | rfl)
  case inst i =>
    simp only [evaluate_inst, StackBitmapPrimitives.inst_withBitmaps]
    cases StackSemInst.instHOL i s <;> rfl
  case shMemOp op r addr =>
    cases addr with
    | addr a off =>
      simp only [evaluate_shMemOp, StackBitmapPrimitives.wordExp_withBitmaps]
      cases wordExp s (.op .add [.var a, .const off]) with
      | none => rfl
      | some value =>
        by_cases zero : s.clock = 0
        · simp [zero,emptyEnv]
        · simp only [zero,if_false]
          exact StackBitmapPrimitives.shMemOp_withBitmaps op r value (decClock s) bitmaps

/-- Adding entries cannot change a nonerror result of any ordinary atomic
clause with an empty dynamic-code oracle. -/
theorem ordinary_append {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width)) (ordinary : Ordinary p)
    (empty : StackEmptyOracle.EmptyOracle s) :
    evaluate (p,{s with bitmaps := s.bitmaps ++ extra}) =
      Prod.map id (fun post => {post with bitmaps := post.bitmaps ++ extra}) (evaluate (p,s)) := by
  rw [ordinary_withBitmaps p s _ ordinary]
  have same := (StackEmptyOracle.preserved p s empty).2.1
  simp only [Prod.map, id_eq]
  rw [same]

private theorem copy_result {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 : Nat) (s : StackSemStateFiniteExact width C F) :
    (StackSemStoreConsts.storeConstSem (resultWidth := width) t1 t2 s).1 = none ∨
    (StackSemStoreConsts.storeConstSem (resultWidth := width) t1 t2 s).1 = some .error := by
  unfold StackSemStoreConsts.storeConstSem
  repeat' first | split | simp_all

private theorem load_result {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (s : StackSemStateFiniteExact width C F) :
    (StackSemSizeBitmapCases.bitmapLoad r v s).1 = none ∨
    (StackSemSizeBitmapCases.bitmapLoad r v s).1 = some .error := by
  unfold StackSemSizeBitmapCases.bitmapLoad
  repeat' first | split | simp_all

/-- Successful constant stores lift to the evaluator clause with all of its
actual guards; nonerror forces the primitive's normal result. -/
theorem storeConsts_append {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 : Nat) (stub : Option Nat) (s post : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width)) (res : Option (StackSemResult width))
    (notError : res ≠ some .error)
    (run : evaluate (.storeConsts t1 t2 stub,s) = (res,post)) :
    evaluate (.storeConsts t1 t2 stub,{s with bitmaps := s.bitmaps ++ extra}) =
      (res,{post with bitmaps := post.bitmaps ++ extra}) := by
  rw [evaluate_storeConsts] at run ⊢
  dsimp only
  split at run
  · cases run; contradiction
  · rename_i enabled
    rw [if_neg enabled]
    split at run
    · cases run; contradiction
    · rename_i allocated
      rw [if_neg allocated]
      split at run
      · cases run; contradiction
      · rename_i checked
        rw [if_neg checked]
        have normal : res = none := by
          have result := copy_result t1 t2 s
          rw [run] at result
          exact result.resolve_right notError
        subst res
        exact StackBitmapAccess.storeConstSem_append t1 t2 s post extra run

/-- Nonerror bitmap-load executions are preserved by table extension. -/
theorem bitmapLoad_append {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (s post : StackSemStateFiniteExact width C F)
    (extra : List (BitVec width)) (res : Option (StackSemResult width))
    (notError : res ≠ some .error)
    (run : evaluate (.bitmapLoad r v,s) = (res,post)) :
    evaluate (.bitmapLoad r v,{s with bitmaps := s.bitmaps ++ extra}) =
      (res,{post with bitmaps := post.bitmaps ++ extra}) := by
  rw [evaluate, evaluateHOL_bitmapLoad] at run ⊢
  have normal : res = none := by
    have result := load_result r v s
    rw [run] at result
    exact result.resolve_right notError
  subst res
  exact StackBitmapAccess.bitmapLoad_append r v s post extra run

end InitECandidate.Solver.Wave8Stage.StackBitmapAtomic
