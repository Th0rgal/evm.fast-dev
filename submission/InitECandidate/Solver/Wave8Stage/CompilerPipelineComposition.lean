import Flapjack.Pancake.PanToWord

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.CompilerPipelineComposition
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

theorem assemble {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (original decoded simplified structured globals : List (DeclHOL width))
    (crep : List (MlS × List Nat × CrepProgHOL width))
    (loop : List (Nat × List Nat × HolLoopProg width))
    (word : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (decodeRun : original = decoded)
    (simpRun : panSimpDeclsHOL decoded = simplified)
    (structRun : Pancake.PanStructs.CompileShapeExact.compileTopExact simplified = structured)
    (globalRun : compileTopExactHOL structured (ofString "main") = globals)
    (crepRun : compileProgDeclsHOLW globals = crep)
    (loopRun : compileProgHOLExact arch crep = loop)
    (wordRun : loopToWordCompileHOL loop = word) :
    panToWordCompileProgHOL arch original = word := by
  simp only [panToWordCompileProgHOL, decodeRun, simpRun, structRun, globalRun,
    crepRun, loopRun, wordRun]

end InitECandidate.Solver.Wave8Stage.CompilerPipelineComposition
