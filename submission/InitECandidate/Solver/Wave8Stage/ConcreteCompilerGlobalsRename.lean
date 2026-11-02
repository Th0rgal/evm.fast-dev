import InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsMeta

set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsRename
open InitE Flapjack Lean
open Flapjack.Basis.Pure.MlString

local cbv_simproc ↓ freezeCodec (Flapjack.Pancake.PanLang.progToHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeSimp (panSimpCompileHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeStruct (Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezePerm (fpermHOL _ _ _) := fun _ => return .rfl (done := true)

open Flapjack.Pancake.PanLang

def renameDeclaration (f g : MlS) (declaration : DeclHOL 64) : DeclHOL 64 :=
  match declaration with
  | .function function => .function { function with
      name := fpermName f g function.name
      body := fpermHOL f g function.body }
  | declaration => declaration

theorem declarations_eq_map (f g : MlS) (declarations : List (DeclHOL 64)) :
    fpermDecsHOL f g declarations = declarations.map (renameDeclaration f g) := by
  induction declarations with
  | nil => simp [fpermDecsHOL]
  | cons declaration rest ih =>
    cases declaration <;> simp [fpermDecsHOL, renameDeclaration, ih]

wave8_list_spine rendered := ConcreteCompilerGlobalsMeta.resorted.map
  (renameDeclaration (ofString "main") ConcreteCompilerGlobalsMeta.newName)
noncomputable def renamed := rendered
theorem renamed_eq : fpermDecsHOL (ofString "main")
    ConcreteCompilerGlobalsMeta.newName ConcreteCompilerGlobalsMeta.resorted = renamed :=
  (declarations_eq_map _ _ _).trans rendered_eq

#print axioms renamed_eq
end InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsRename
