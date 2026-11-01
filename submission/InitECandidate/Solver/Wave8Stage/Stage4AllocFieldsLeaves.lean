import InitECandidate.Solver.Wave8Stage.Stage4RuntimeEval

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.AllocFields
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack.StackSemExpressions Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width]

/-- Replace only allocation machinery and installation callbacks. -/
def override {C F : Type} (s cfg : StackSemStateFiniteExact width C F) :=
  { s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }

def replaceResult {C F : Type} (cfg : StackSemStateFiniteExact width C F)
    (out : Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  (out.1, override out.2 cfg)

theorem wordExp_withAllocFields {C F : Type} (s : StackSemStateFiniteExact width C F)
    (cfg : StackSemStateFiniteExact width C F) : ∀ e,
    wordExp { s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle } e = wordExp s e
  | .const _ | .var _ | .lookup _ => by simp only [wordExp]
  | .load e => by simp only [wordExp, wordExp_withAllocFields s cfg e]; rfl
  | .shift sh a b => by simp only [wordExp, wordExp_withAllocFields s cfg a, wordExp_withAllocFields s cfg b]
  | .op op es => by
    have hm : es.attach.map (fun e => wordExp { s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle } e.val) =
        es.attach.map (fun e => wordExp s e.val) := by
      apply List.map_congr_left
      intro e he
      exact wordExp_withAllocFields s cfg e.val
    simp only [wordExp, hm]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have hm := List.sizeOf_lt_of_mem e.property; omega)

theorem instHOL_withAllocFields {C F : Type} (s : StackSemStateFiniteExact width C F)
    (cfg : StackSemStateFiniteExact width C F) (i : HolInst width) :
    StackSemInst.instHOL i { s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle } =
      (StackSemInst.instHOL i s).map (fun t => { t with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }) := by
  cases i
  case' arith op => cases op
  case' mem op r addr => cases op <;> cases addr
  all_goals simp only [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    Option.join, Option.bind_some, id_eq, assign, wordExp_withAllocFields,
    StackSemStateOps.getVars, getVar, memLoad, memStore]
  all_goals repeat' (first | rfl | (split <;> try simp_all [setVar]))

theorem shMemOp_withAllocFields {C F : Type} (s : StackSemStateFiniteExact width C F)
    (cfg : StackSemStateFiniteExact width C F) (op : WordMemOp) (r : Nat) (addr : BitVec width) :
    StackSemShMem.shMemOp op r addr { s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle } =
      replaceResult cfg (StackSemShMem.shMemOp op r addr s) := by
  cases op <;> simp only [StackSemShMem.shMemOp,
    StackSemShMem.shMemLoad, StackSemShMem.shMemStore,
    StackSemShMem.shMemLoadByte, StackSemShMem.shMemStoreByte,
    StackSemShMem.shMemLoad16, StackSemShMem.shMemStore16,
    StackSemShMem.shMemLoad32, StackSemShMem.shMemStore32, getVar]
  all_goals repeat' split
  all_goals simp_all only [replaceResult, override]

theorem leaf_evaluate_withAllocFields {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (cfg : StackSemStateFiniteExact width C F) (hp : LeafAllowed bad p) :
    evaluate (p, { s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }) = replaceResult cfg (evaluate (p, s)) := by
  cases p <;> simp only [LeafAllowed] at hp
  case locValue r label entry =>
    simp only [evaluate_locValue]
    split <;> simp_all only [replaceResult, override, setVar]
  case inst i =>
    simp only [evaluate_inst, instHOL_withAllocFields]
    cases StackSemInst.instHOL i s <;> rfl
  case shMemOp op r addr =>
    cases addr with
    | addr a w =>
      simp only [evaluate_shMemOp, wordExp_withAllocFields]
      split
      · split
        · rfl
        · exact shMemOp_withAllocFields (decClock s) cfg op r _
      · rfl
  all_goals simp only [evaluate_skip, evaluate_halt, evaluate_get, evaluate_set,
    evaluate_opCurrHeap, evaluate_tick, evaluate_ret, evaluate_raise, evaluate_break,
    evaluate_continue, evaluate_stackAlloc, evaluate_stackFree,
    evaluate_stackLoad, evaluate_stackStore, evaluate_stackLoadAny, evaluate_stackStoreAny,
    evaluate_stackGetSize, evaluate_stackSetSize, evaluate_bitmapLoad,
    evaluate_codeBufferWrite, evaluate_dataBufferWrite, evaluate_ffi,
    getVar, wordExp_withAllocFields]
  all_goals repeat' split
  all_goals simp_all only [replaceResult, override, emptyEnv, setVar, setStore, decClock]

theorem install_evaluate_withAllocFields {C F : Type}
    (a b c d e : Nat) (s : StackSemStateFiniteExact width C F)
    (cfg : StackSemStateFiniteExact width C F) (ho : ∀ i, (s.compileOracle i).2.1 = [])
    (ht : ∀ i, (cfg.compileOracle i).2.1 = []) :
    evaluate (.install a b c d e, { s with useAlloc := cfg.useAlloc, gcFun := cfg.gcFun, compile := cfg.compile, compileOracle := cfg.compileOracle }) =
      replaceResult cfg (evaluate (.install a b c d e, s)) := by
  simp only [evaluate_install, ho 0, ht 0, getVar]
  repeat' split
  all_goals first | contradiction | simp_all only [replaceResult, override]

#print axioms leaf_evaluate_withAllocFields
end InitECandidate.Solver.Wave8Stage.AllocFields
