import InitECandidate.Solver.Wave8Stage.ConcreteCompilerStruct

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option Elab.async false

namespace InitECandidate.Solver.Wave8Stage.CompilerFunctionNames
open Flapjack Flapjack.Pancake.PanLang Flapjack.Pancake.PanStructs.CompileShapeExact

def names (declarations : List (DeclHOL 64)) := (functionsHOL declarations).map Prod.fst

theorem simplify (declarations : List (DeclHOL 64)) :
    names (declarations.map ConcreteCompilerSimp.simplifyDeclaration) = names declarations := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
    cases declaration <;> simp [names, ConcreteCompilerSimp.simplifyDeclaration, functionsHOL,
      List.map, names] at ih ⊢ <;> exact ih

theorem structureCompile (context : ContextExact) (declarations : List (DeclHOL 64)) :
    names (compileDeclsExact context declarations).1 = names declarations := by
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration rest ih =>
    cases declaration <;> simp [compileDeclsExact, names, functionsHOL,
      show ∀ c, (functionsHOL (compileDeclsExact c rest).1).map Prod.fst =
        (functionsHOL rest).map Prod.fst from ih]

theorem concrete : names ConcreteCompilerStruct.source = names ConcreteCompilerSource.source := by
  rw [← ConcreteCompilerStruct.source_eq]
  change names (compileDeclsExact _ ConcreteCompilerSimp.source).1 = _
  rw [structureCompile]
  change names ConcreteCompilerSimp.rendered = _
  rw [← ConcreteCompilerSimp.rendered_eq]
  exact simplify _

#print axioms concrete
end InitECandidate.Solver.Wave8Stage.CompilerFunctionNames
