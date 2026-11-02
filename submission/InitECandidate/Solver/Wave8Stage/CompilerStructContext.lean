import InitECandidate.Solver.Wave8Stage.ConcreteCompilerSimp
import InitECandidate.Solver.Wave8Stage.CompilerMetadataReduction

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace InitECandidate.Solver.Wave8Stage.CompilerStructContext
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact

def finalContext (context : ContextExact) : List (DeclHOL 64) → ContextExact
  | [] => context
  | .decl shape name _ :: rest =>
      finalContext { context with globals := (name, shape) :: context.globals } rest
  | _ :: rest => finalContext context rest

open Lean Meta in
cbv_simproc ↓ reduceFinalContext (finalContext _ _) := fun expression => do
  let result ← withTransparency .all (whnf expression)
  return .step result (← mkEqRefl expression)

def render (context final : ContextExact) : List (DeclHOL 64) → List (DeclHOL 64)
  | [] => []
  | .decl shape name value :: rest =>
      .decl (compileShapeExact context.structs shape) name (compileExpExact context value) ::
        render { context with globals := (name, shape) :: context.globals } final rest
  | .function declaration :: rest =>
      .function { declaration with
        params := declaration.params.map fun p => (p.1, compileShapeExact context.structs p.2)
        body := compileProgExact { final with locals := declaration.params } declaration.body
        returnShape := compileShapeExact context.structs declaration.returnShape } ::
        render context final rest
  | .name _ _ :: rest => render context final rest
  | .exnDecl name shape :: rest =>
      .exnDecl name (compileShapeExact context.structs shape) :: render context final rest

theorem compile_eq (context : ContextExact) (declarations : List (DeclHOL 64)) :
    compileDeclsExact context declarations =
      (render context (finalContext context declarations) declarations,
        finalContext context declarations) := by
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration rest ih =>
    cases declaration <;> simp only [compileDeclsExact, render, finalContext, ih]

#print axioms compile_eq
end InitECandidate.Solver.Wave8Stage.CompilerStructContext
