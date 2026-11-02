import InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsDecs
import InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsInput
import InitECandidate.Solver.Wave8Stage.GlobalTopComposition

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobals
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

noncomputable def source : List (DeclHOL 64) :=
  GlobalTopComposition.build ConcreteCompilerGlobalsMeta.newName
    ConcreteCompilerGlobalsDecs.compiled

theorem compile_eq :
    compileTopExactHOL ConcreteCompilerStruct.source (ofString "main") = source := by
  exact GlobalTopComposition.assemble
    ConcreteCompilerStruct.source
    ConcreteCompilerGlobalsInput.head ConcreteCompilerGlobalsInput.tail
    ConcreteCompilerGlobalsMeta.resorted ConcreteCompilerGlobalsRename.renamed
    ConcreteCompilerGlobalsMeta.newName ConcreteCompilerGlobalsInit.initial
    ConcreteCompilerGlobalsDecs.compiled
    ConcreteCompilerGlobalsInput.codeShape
    ConcreteCompilerGlobalsInput.headName
    ConcreteCompilerGlobalsInput.headParams
    ConcreteCompilerGlobalsInput.headShape
    ConcreteCompilerGlobalsMeta.resorted_eq
    ConcreteCompilerGlobalsMeta.newName_eq
    ConcreteCompilerGlobalsRename.renamed_eq
    ConcreteCompilerGlobalsInit.initial_eq
    ConcreteCompilerGlobalsDecs.compile_eq

end InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobals
