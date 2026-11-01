import InitECandidate.Solver.Wave8Stage.Stage4RuntimeEval

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.StackSemExpressions Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width]

def replaceResultCode {C F : Type} (code : Spt (HolProg width))
    (out : Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  (out.1, { out.2 with code := code })

theorem wordExp_withCode {C F : Type} (s : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) : ∀ e,
    wordExp { s with code := code } e = wordExp s e
  | .const _ | .var _ | .lookup _ => by simp only [wordExp]
  | .load e => by simp only [wordExp, wordExp_withCode s code e]; rfl
  | .shift sh a b => by simp only [wordExp, wordExp_withCode s code a, wordExp_withCode s code b]
  | .op op es => by
    have hm : es.attach.map (fun e => wordExp { s with code := code } e.val) =
        es.attach.map (fun e => wordExp s e.val) := by
      apply List.map_congr_left
      intro e he
      exact wordExp_withCode s code e.val
    simp only [wordExp, hm]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have hm := List.sizeOf_lt_of_mem e.property; omega)

theorem instHOL_withCode {C F : Type} (s : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) (i : HolInst width) :
    StackSemInst.instHOL i { s with code := code } =
      (StackSemInst.instHOL i s).map (fun t => { t with code := code }) := by
  cases i
  case' arith op => cases op
  case' mem op r addr => cases op <;> cases addr
  all_goals simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    Option.join, Option.bind_some, id_eq, assign, wordExp_withCode,
    StackSemStateOps.getVars, getVar, memLoad, memStore]
  all_goals repeat' (first | rfl | (split <;> try simp_all [setVar]))

theorem shMemOp_withCode {C F : Type} (s : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) (op : WordMemOp) (r : Nat) (addr : BitVec width) :
    StackSemShMem.shMemOp op r addr { s with code := code } =
      replaceResultCode code (StackSemShMem.shMemOp op r addr s) := by
  cases op <;> simp only [StackSemShMem.shMemOp,
    StackSemShMem.shMemLoad, StackSemShMem.shMemStore,
    StackSemShMem.shMemLoadByte, StackSemShMem.shMemStoreByte,
    StackSemShMem.shMemLoad16, StackSemShMem.shMemStore16,
    StackSemShMem.shMemLoad32, StackSemShMem.shMemStore32, getVar]
  all_goals repeat' split
  all_goals simp_all only [replaceResultCode]

theorem leaf_evaluate_withCode {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) (hp : LeafAllowed bad p)
    (hloc : ∀ n k, n ≠ bad →
      (StackSem.locCheckExact code (n, k) ↔ StackSem.locCheckExact s.code (n, k))) :
    evaluate (p, { s with code := code }) = replaceResultCode code (evaluate (p, s)) := by
  cases p <;> simp only [LeafAllowed] at hp
  case locValue r label entry =>
    simp only [evaluate_locValue]
    rw [propext (hloc label entry hp)]
    split <;> simp_all only [replaceResultCode, setVar]
  case inst i =>
    simp only [evaluate_inst, instHOL_withCode]
    cases StackSemInst.instHOL i s <;> rfl
  case shMemOp op r addr =>
    cases addr with
    | addr a w =>
      simp only [evaluate_shMemOp, wordExp_withCode]
      split
      · split
        · rfl
        · exact shMemOp_withCode (decClock s) code op r _
      · rfl
  all_goals simp only [evaluate_skip, evaluate_halt, evaluate_get, evaluate_set,
    evaluate_opCurrHeap, evaluate_tick, evaluate_ret, evaluate_raise, evaluate_break,
    evaluate_continue, evaluate_stackAlloc, evaluate_stackFree,
    evaluate_stackLoad, evaluate_stackStore, evaluate_stackLoadAny, evaluate_stackStoreAny,
    evaluate_stackGetSize, evaluate_stackSetSize, evaluate_bitmapLoad,
    evaluate_codeBufferWrite, evaluate_dataBufferWrite, evaluate_ffi,
    getVar, wordExp_withCode]
  all_goals repeat' split
  all_goals simp_all only [replaceResultCode, emptyEnv, setVar, setStore, decClock]

theorem install_evaluate_withCode {C F : Type}
    (a b c d e : Nat) (s : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) (ho : ∀ i, (s.compileOracle i).2.1 = []) :
    evaluate (.install a b c d e, { s with code := code }) =
      replaceResultCode code (evaluate (.install a b c d e, s)) := by
  simp only [evaluate_install, ho 0, getVar]
  repeat' split
  all_goals first | contradiction | simp_all only [replaceResultCode]

#print axioms leaf_evaluate_withCode
end InitECandidate.Solver.Wave8Stage.RuntimeLabels
