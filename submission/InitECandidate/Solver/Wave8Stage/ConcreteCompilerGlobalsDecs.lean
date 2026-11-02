import InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsFunctions
import InitECandidate.Solver.Wave8Stage.GlobalDeclarationComposition

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsDecs
open Flapjack


noncomputable def compiled :=
  (ConcreteCompilerGlobalsHeader.compiled.fst,
    ConcreteCompilerGlobalsHeader.compiled.snd.fst ++ ConcreteCompilerGlobalsFunctions.compiled,
    ConcreteCompilerGlobalsHeader.compiled.snd.snd.fst, ConcreteCompilerGlobalsHeader.compiled.snd.snd.snd)

theorem compile_eq : compileDecsExactHOL ConcreteCompilerGlobalsInit.initial
    ConcreteCompilerGlobalsRename.renamed = compiled := by
  exact GlobalDeclarationComposition.assemble ConcreteCompilerGlobalsInit.initial
    ConcreteCompilerGlobalsRename.renamed ConcreteCompilerGlobalsSplit.header
    ConcreteCompilerGlobalsSplit.functions ConcreteCompilerGlobalsHeader.compiled
    ConcreteCompilerGlobalsFunctions.compiled ConcreteCompilerGlobalsSplit.split
    ConcreteCompilerGlobalsHeader.compiled_eq ConcreteCompilerGlobalsSplit.allFunctions
    ConcreteCompilerGlobalsFunctions.compiled_eq

#print axioms compile_eq
end InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsDecs
