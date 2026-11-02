import InitECandidate.Solver.Wave8Stage.Stage4RuntimeInstructions

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
variable {width : Nat} [NeZero width]

theorem writeBytearray_safe {bad : Nat} {domain : BitVec width → Bool}
    {memory : BitVec width → WordLocW width} (hm : MemorySafe bad domain memory)
    (be : Bool) (addr : BitVec width) (bytes : List (BitVec 8)) :
    MemorySafe bad domain (writeBytearrayExact addr bytes memory domain be) := by
  induction bytes generalizing addr with
  | nil => exact hm
  | cons b bs ih =>
    simp only [writeBytearrayExact]
    split
    · exact memStoreByte_safe (ih _) _ _ _ (by assumption)
    · exact hm

theorem StateSafe.stackSet_safe {C F : Type} {bad : Nat}
    {s : StackSemStateFiniteExact width C F} (h : StateSafe bad s)
    (n : Nat) (v : WordLocW width) (hv : ValueSafe bad v) :
    StateSafe bad { s with stack := s.stack.set n v } := by
  refine ⟨h.regs, h.store, ?_, h.memory⟩
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h.stack x hx
  · exact hv

theorem StateSafe.shMemOp_safe {C F : Type} {bad : Nat}
    {s : StackSemStateFiniteExact width C F} (h : StateSafe bad s)
    (op : WordMemOp) (r : Nat) (addr : BitVec width) :
    StateSafe bad (StackSemShMem.shMemOp op r addr s).2 := by
  cases op <;> simp only [StackSemShMem.shMemOp,
    StackSemShMem.shMemLoad, StackSemShMem.shMemStore,
    StackSemShMem.shMemLoadByte, StackSemShMem.shMemStoreByte,
    StackSemShMem.shMemLoad16, StackSemShMem.shMemStore16,
    StackSemShMem.shMemLoad32, StackSemShMem.shMemStore32]
  all_goals repeat' split
  all_goals first
    | exact ⟨h.regs, h.store, h.stack, h.memory⟩
    | exact ⟨mapSafe_update h.regs _ _ trivial, h.store, h.stack, h.memory⟩

/-- Nonrecursive evaluator clauses that do not allocate, install code, or
store constants. The label constructor must itself avoid the excluded label. -/
def LeafAllowed (bad : Nat) : HolProg width → Prop
  | .seq .. | .ite .. | .loop .. | .jumpLower .. | .rawCall .. | .call .. => False
  | .alloc .. | .install .. | .storeConsts .. => False
  | .locValue _ label _ => label ≠ bad
  | _ => True

theorem leaf_evaluate_safe {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hp : LeafAllowed bad p) (h : StateSafe bad s) :
    StateSafe bad (evaluate (p, s)).2 := by
  cases p <;> simp only [LeafAllowed] at hp
  case inst i =>
    rw [evaluate_inst]
    split
    · exact h.instHOL_safe i (by assumption)
    · exact h
  case shMemOp op r addr =>
    cases addr with
    | addr a w =>
      rw [evaluate_shMemOp]
      split
      · split
        · exact h.emptyEnv_safe
        · exact (h.withClock _).shMemOp_safe op r _
      · exact h
  case stackSetSize r =>
    rw [evaluate_stackSetSize]
    repeat' split
    all_goals first
      | exact h
      | exact h.emptyEnv_safe
      | (apply StateSafe.setVar_safe; exact ⟨h.regs, h.store, h.stack, h.memory⟩; trivial)
  all_goals simp only [evaluate_skip, evaluate_halt, evaluate_get, evaluate_set,
    evaluate_opCurrHeap, evaluate_tick, evaluate_ret, evaluate_raise, evaluate_break,
    evaluate_continue, evaluate_locValue, evaluate_stackAlloc, evaluate_stackFree,
    evaluate_stackLoad, evaluate_stackStore, evaluate_stackLoadAny, evaluate_stackStoreAny,
    evaluate_stackGetSize, evaluate_bitmapLoad,
    evaluate_codeBufferWrite, evaluate_dataBufferWrite, evaluate_ffi]
  all_goals repeat' split
  all_goals first
    | exact ⟨h.regs, h.store, h.stack, h.memory⟩
    | exact h.emptyEnv_safe
    | exact h.setVar_word _ _
    | exact h.setVar_safe _ _ hp
    | exact h.setVar_safe _ _ (h.store _ _ (by assumption))
    | exact h.setStore_safe _ _ (h.regs _ _ (by assumption))
    | exact h.setVar_safe _ _ (h.stack _ (List.getElem_mem _))
    | exact h.stackSet_safe _ _ (h.regs _ _ (by assumption))
    | exact StateSafe.setVar_safe ⟨h.regs, h.store, h.stack, h.memory⟩ _ _ trivial
    | exact ⟨mapSafe_restrict h.regs _, h.store, h.stack, writeBytearray_safe h.memory _ _ _⟩

/-- An empty installation oracle keeps both installed code and the emptiness
of future oracle code intact, for every evaluation (including failures). -/
theorem evaluate_code_empty_oracle {C F : Type}
    (p : HolProg width) (s post : StackSemStateFiniteExact width C F)
    (res : Option (StackSemResult width)) (run : evaluate (p, s) = (res, post))
    (ho : ∀ i, (s.compileOracle i).2.1 = []) :
    post.code = s.code ∧ ∀ i, (post.compileOracle i).2.1 = [] := by
  obtain ⟨n, hor, hc, _⟩ := StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps p s res post run
  have union_nil : ∀ (t : Spt (HolProg width)), sptUnion t .ln = t := by
    intro t
    cases t <;> simp [sptUnion]
  have fold : ∀ (is : List Nat) (t : Spt (HolProg width)),
      (is.map (fun i => sptFromAList (s.compileOracle i).2.1)).foldl sptUnion t = t := by
    intro is t
    induction is generalizing t with
    | nil => rfl
    | cons i is ih =>
      simp only [List.map_cons, List.foldl_cons, ho i]
      rw [show sptFromAList ([] : List (Nat × HolProg width)) = .ln from rfl, union_nil]
      exact ih t
  refine ⟨hc.trans (fold _ _), ?_⟩
  intro i
  rw [hor]
  exact ho _

end InitECandidate.Solver.Wave8Stage.RuntimeLabels
