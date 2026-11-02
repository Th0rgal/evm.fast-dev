import InitECandidate.Solver.Wave8Stage.Stage4CodeLeaves

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8Stage.RuntimeLabels
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.StackSemExpressions Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width]

/-- Existing sections are preserved; extra sections may be added. -/
def CodeExtension (source target : Spt (HolProg width)) : Prop :=
  ∀ n p, sptLookup n source = some p → sptLookup n target = some p

theorem CodeExtension.labels {source target : Spt (HolProg width)}
    (h : CodeExtension source target) (n k : Nat) :
    StackSem.locCheckExact source (n, k) → StackSem.locCheckExact target (n, k) := by
  rintro (⟨hk, hd⟩ | ⟨label, p, hp, hl⟩)
  · refine Or.inl ⟨hk, ?_⟩
    simp only [sptMem, sptDomain] at hd ⊢
    cases he : sptLookup n source with
    | none => simp [he] at hd
    | some p => simp [h n p he]
  · exact Or.inr ⟨label, p, h label p hp, hl⟩

theorem CodeExtension.findCode {source target : Spt (HolProg width)}
    (h : CodeExtension source target) (regs : HolFiniteMapExact Nat (WordLocW width))
    (dest : Nat ⊕ Nat) (p : HolProg width) :
    findCode dest regs source = some p → findCode dest regs target = some p := by
  cases dest <;> dsimp only [StackSemControl.findCode]
  · exact h _ p
  · repeat' split
    all_goals first | exact h _ p | (intro he; cases he)

theorem CodeExtension.after_evaluate {C F : Type}
    {s : StackSemStateFiniteExact width C F} {code : Spt (HolProg width)}
    (h : CodeExtension s.code code) (p : HolProg width)
    (ho : ∀ i, (s.compileOracle i).2.1 = []) :
    CodeExtension (evaluate (p, s)).2.code code := by
  have he : (evaluate (p, s)).2.code = s.code :=
    (evaluate_code_empty_oracle p s _ _ rfl ho).1
  rw [he]
  exact h

theorem leaf_evaluate_extendCode {C F : Type} {bad : Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) (hp : LeafAllowed bad p)
    (he : CodeExtension s.code code)
    (hne : (evaluate (p, s)).1 ≠ some .error) :
    evaluate (p, { s with code := code }) = replaceResultCode code (evaluate (p, s)) := by
  cases p <;> simp only [LeafAllowed] at hp
  case locValue r label entry =>
    by_cases hl : StackSem.locCheckExact s.code (label, entry)
    · simp only [evaluate_locValue, if_pos hl, if_pos (he.labels label entry hl)]
      rfl
    · simp [evaluate_locValue, hl] at hne
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

end InitECandidate.Solver.Wave8Stage.RuntimeLabels
