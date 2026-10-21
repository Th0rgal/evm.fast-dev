import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.InitializersData
import InitECandidate.Proofs.FrontendStages.Globals.HeaderFacts
import InitECandidate.Proofs.GlobalsComposition

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack Flapjack.Pancake.PanLang


theorem compileGlobals_eq : compileDecsExactHOL globalInitial globalDeclarations =
    (globalInitializers, [], [], globalContext) := by
  rw [InitECandidate.Proofs.GlobalsKernelComputation.compileDecs_function_eq,
    globalDeclarations_structural_eq, globalInitializers_structural_eq,
    globalContext_structural_eq]
  kernel_rfl

theorem renameGlobals_eq : fpermDecsHOL globalStart globalNewStart globalDeclarations = globalDeclarations := by
  rw [InitECandidate.Proofs.GlobalsComputation.fpermDecs_eq_map, globalDeclarations_structural_eq]
  kernel_rfl

theorem compileExceptions_eq (context : PanGlobalsContextExact 64) :
    compileDecsExactHOL context exceptionDeclarations = ([], [], exceptionDeclarations, context) := by
  simp only [exceptionDeclarations, simplified3, simplifiedData3, simplified105, simplifiedData105, simplified182, simplifiedData182, simplified217, simplifiedData217, simplified218, simplifiedData218, simplified237, simplifiedData237, simplified292, simplifiedData292, simplified344, simplifiedData344, simplified432, simplifiedData432, simplified841, simplifiedData841, declToHOL, compileDecsExactHOL]

theorem renameExceptions_eq : fpermDecsHOL globalStart globalNewStart exceptionDeclarations = exceptionDeclarations := by
  simp only [exceptionDeclarations, simplified3, simplifiedData3, simplified105, simplifiedData105, simplified182, simplifiedData182, simplified217, simplifiedData217, simplified218, simplifiedData218, simplified237, simplifiedData237, simplified292, simplifiedData292, simplified344, simplifiedData344, simplified432, simplifiedData432, simplified841, simplifiedData841, declToHOL, fpermDecsHOL]

#print axioms compileGlobals_eq
#print axioms renameGlobals_eq
#print axioms compileExceptions_eq
#print axioms renameExceptions_eq
end InitECandidate.Proofs.FrontendStages.Declarations
