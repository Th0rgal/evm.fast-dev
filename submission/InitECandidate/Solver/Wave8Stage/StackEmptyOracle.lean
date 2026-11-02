import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.StackEmptyOracle
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

/-- Every dynamic-code oracle entry supplies no code or bitmaps. -/
def EmptyOracle {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ index, (s.compileOracle index).2.1 = [] ∧ (s.compileOracle index).2.2 = []

private theorem fold_empty {α β : Type} (indices : List Nat) (f : Nat → List (Nat × α) × β)
    (empty : ∀ i, (f i).1 = []) (initial : Spt α) :
    ((indices.map (fun i => sptFromAList (f i).1)).foldl sptUnion initial) = initial := by
  induction indices generalizing initial with
  | nil => rfl
  | cons index rest ih =>
    simp only [List.map_cons,List.foldl_cons,empty,sptFromAList]
    have union : sptUnion initial .ln = initial := by cases initial <;> simp only [sptUnion]
    rw [union]
    simpa only [empty,sptFromAList] using ih initial

/-- Empty dynamic-code oracles keep the code and bitmap tables fixed under
all actual Stack evaluation, and the shifted oracle remains empty. -/
theorem preserved {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (empty : EmptyOracle s) :
    (StackSemEvaluate.evaluate (p,s)).2.code = s.code ∧
    (StackSemEvaluate.evaluate (p,s)).2.bitmaps = s.bitmaps ∧
    EmptyOracle (StackSemEvaluate.evaluate (p,s)).2 := by
  obtain ⟨count,oracle,code,bitmaps⟩ := EvaluateCodeBitmaps.evaluateCodeBitmaps p s _ _ rfl
  change (StackSemEvaluate.evaluateHOL p s).2.code = s.code ∧
    (StackSemEvaluate.evaluateHOL p s).2.bitmaps = s.bitmaps ∧
    EmptyOracle (StackSemEvaluate.evaluateHOL p s).2
  refine ⟨?_,?_,?_⟩
  · rw [code]
    exact fold_empty _ (fun i => (s.compileOracle i).2) (fun i => (empty i).1) s.code
  · rw [bitmaps]
    have mapped : (List.range count).map (fun i => (s.compileOracle i).2.2) =
        (List.range count).map (fun _ => ([] : List (BitVec width))) := by
      apply List.map_congr_left
      intro i member
      exact (empty i).2
    rw [mapped]
    simp
  · intro index
    rw [oracle]
    exact empty (index+count)

#print axioms preserved
end InitECandidate.Solver.Wave8Stage.StackEmptyOracle
