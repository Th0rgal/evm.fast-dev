import InitECandidate.Solver.Wave8Stage.ConcreteCompilerSource
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000
open InitE Flapjack Lean
/-! Kernel-certified declaration-list structure; function-body reductions
are deliberately deferred to the individual concrete function checks. -/

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerSimp
open Flapjack.Pancake.PanLang

/-- Expose the declaration-list recursion without reducing any program body or
the well-founded source function's size-of termination measure. -/
def simplifyDeclaration (declaration : DeclHOL 64) : DeclHOL 64 :=
  match declaration with
  | .function function => .function { function with body := panSimpCompileHOL function.body }
  | declaration => declaration

theorem declarations_eq_map (declarations : List (DeclHOL 64)) :
    panSimpDeclsHOL declarations = declarations.map simplifyDeclaration := by
  induction declarations with
  | nil => simp [panSimpDeclsHOL]
  | cons declaration rest ih =>
    cases declaration <;> simp [panSimpDeclsHOL, simplifyDeclaration, ih]

wave8_list_spine rendered := ConcreteCompilerSource.source.map simplifyDeclaration
noncomputable def source := rendered
theorem source_eq : panSimpDeclsHOL ConcreteCompilerSource.source = source :=
  (declarations_eq_map _).trans rendered_eq
end InitECandidate.Solver.Wave8Stage.ConcreteCompilerSimp
