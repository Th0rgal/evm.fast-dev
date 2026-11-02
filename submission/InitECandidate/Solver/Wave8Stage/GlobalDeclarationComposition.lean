import Flapjack.Pancake.Proofs.PanGlobals.CompileDecsStructural

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.GlobalDeclarationComposition
open Flapjack Flapjack.Pancake.PanLang

/-- Compiling a function-only suffix changes each body at the fixed globals
context. No initializer, exception, or context change is produced. -/
theorem functions {width : Nat} [NeZero width] (context : PanGlobalsContextExact width)
    (declarations : List (DeclHOL width))
    (allFunctions : ∀ declaration ∈ declarations, isFunctionHOL declaration = true) :
    compileDecsExactHOL context declarations = ([], declarations.map (fun declaration =>
      match declaration with
      | .function function => .function { function with body := compileProgExactHOL context function.body }
      | _ => .name (Flapjack.Basis.Pure.MlString.ofString "") []), [], context) := by
  rcases run : compileDecsExactHOL context declarations with ⟨initializers,compiled,exceptions,final⟩
  obtain ⟨rfl,rfl,rfl,rfl⟩ :=
    PanGlobalsCompileDecsStructural.compile_decs_functions_thmHOL context declarations
      initializers compiled exceptions final ⟨run,allFunctions⟩
  rfl

#print axioms functions
#print axioms PanGlobalsCompileDecsStructural.compile_decls_appendHOL

/-- Assemble header and function-map certificates while the lists and result
remain abstract, avoiding conversion of the concrete function bodies. -/
theorem assemble {width : Nat} [NeZero width] (context : PanGlobalsContextExact width)
    (code header suffix : List (DeclHOL width))
    (result : List (ProgHOL width) × List (DeclHOL width) × List (DeclHOL width) × PanGlobalsContextExact width)
    (compiledFunctions : List (DeclHOL width))
    (split : code = header ++ suffix)
    (headerRun : compileDecsExactHOL context header = result)
    (allFunctions : ∀ declaration ∈ suffix, isFunctionHOL declaration = true)
    (functionMap : suffix.map (fun declaration => match declaration with
      | .function function => DeclHOL.function { function with
          body := compileProgExactHOL result.snd.snd.snd function.body }
      | _ => DeclHOL.name (Flapjack.Basis.Pure.MlString.ofString "") []) = compiledFunctions) :
    compileDecsExactHOL context code =
      (result.fst, result.snd.fst ++ compiledFunctions, result.snd.snd.fst, result.snd.snd.snd) := by
  rw [split, PanGlobalsCompileDecsStructural.compile_decls_appendHOL, headerRun]
  dsimp only
  rw [functions _ _ allFunctions]
  dsimp only
  simp only [List.append_nil]
  rw [← functionMap]

#print axioms assemble
end InitECandidate.Solver.Wave8Stage.GlobalDeclarationComposition
