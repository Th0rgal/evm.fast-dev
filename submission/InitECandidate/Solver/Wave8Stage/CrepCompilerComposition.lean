import Flapjack.Pancake.PanToWord

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.CrepCompilerComposition
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

def lower {width : Nat} [NeZero width]
    (functions : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (eids : HolFiniteMapExact MlS (BitVec width)) :=
  functions.map (fun entry =>
    (entry.1, crepVarsHOL entry.2.1, compFuncExactHOLW fs eids entry.2.1 entry.2.2.1))

theorem assemble {width : Nat} [NeZero width]
    (code : List (DeclHOL width))
    (functions : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (names : List MlS)
    (fs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (eids : HolFiniteMapExact MlS (BitVec width))
    (lowered result : List (MlS × List Nat × CrepProgHOL width))
    (functionsRun : functionsHOL code = functions)
    (namesRun : (functionsHOL (code.filter inlinableHOL)).map Prod.fst = names)
    (fsRun : makeFuncsExactHOL functions = fs)
    (eidsRun : getEidsFromDeclsHOL code = eids)
    (lowerRun : lower functions fs eids = lowered)
    (inlineRun : CrepInlineCanonical.compileInlTopHOLExact names lowered = result) :
    compileProgDeclsHOLW code = result := by
  simp only [compileProgDeclsHOLW, compileToCrepExactHOLW, functionsRun,
    namesRun, fsRun, eidsRun]
  change CrepInlineCanonical.compileInlTopHOLExact names (lower functions fs eids) = result
  rw [lowerRun, inlineRun]

end InitECandidate.Solver.Wave8Stage.CrepCompilerComposition
