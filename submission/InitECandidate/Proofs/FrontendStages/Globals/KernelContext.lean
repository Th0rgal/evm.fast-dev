import InitECandidate.Proofs.GlobalsKernelComputation
import InitECandidate.Proofs.FrontendStages.Globals.InitializersData
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack Flapjack.Pancake.PanLang
def globalDeclarationData : List (Decl (BitVec 64)) := [simplifiedData1, simplifiedData2, simplifiedData5, simplifiedData6, simplifiedData38, simplifiedData90, simplifiedData91, simplifiedData98, simplifiedData99, simplifiedData100, simplifiedData148, simplifiedData183, simplifiedData184, simplifiedData185, simplifiedData234, simplifiedData238, simplifiedData239, simplifiedData240, simplifiedData241, simplifiedData242, simplifiedData345, simplifiedData346, simplifiedData347, simplifiedData348, simplifiedData349, simplifiedData350, simplifiedData400, simplifiedData401, simplifiedData402, simplifiedData403, simplifiedData404, simplifiedData433, simplifiedData434, simplifiedData435, simplifiedData436, simplifiedData559, simplifiedData560, simplifiedData561, simplifiedData562, simplifiedData605, simplifiedData606, simplifiedData607, simplifiedData608, simplifiedData615, simplifiedData616, simplifiedData617, simplifiedData643, simplifiedData644, simplifiedData692, simplifiedData807, simplifiedData842, simplifiedData843, simplifiedData844, simplifiedData845, simplifiedData846, simplifiedData847, simplifiedData848, simplifiedData849, simplifiedData850, simplifiedData851, simplifiedData852, simplifiedData853, simplifiedData854, simplifiedData855, simplifiedData856, simplifiedData860, simplifiedData885]
def globalDeclarationsStructural : List (DeclHOL 64) := globalDeclarationData.map InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural
theorem globalDeclarations_structural_eq : globalDeclarations = globalDeclarationsStructural := by
  simp only [globalDeclarations, globalDeclarationsStructural, globalDeclarationData, simplified1, simplified2, simplified5, simplified6, simplified38, simplified90, simplified91, simplified98, simplified99, simplified100, simplified148, simplified183, simplified184, simplified185, simplified234, simplified238, simplified239, simplified240, simplified241, simplified242, simplified345, simplified346, simplified347, simplified348, simplified349, simplified350, simplified400, simplified401, simplified402, simplified403, simplified404, simplified433, simplified434, simplified435, simplified436, simplified559, simplified560, simplified561, simplified562, simplified605, simplified606, simplified607, simplified608, simplified615, simplified616, simplified617, simplified643, simplified644, simplified692, simplified807, simplified842, simplified843, simplified844, simplified845, simplified846, simplified847, simplified848, simplified849, simplified850, simplified851, simplified852, simplified853, simplified854, simplified855, simplified856, simplified860, simplified885, List.map_cons, List.map_nil, InitECandidate.Proofs.FrontendCodecComputation.declToHOL_function_eq]

def globalCompilationStructural := InitECandidate.Proofs.GlobalsKernelComputation.compileDecsExactHOL globalInitial globalDeclarationsStructural
theorem globalContext_structural_eq : globalContext = globalCompilationStructural.2.2.2 := by
  unfold globalContext globalCompilationStructural
  rw [InitECandidate.Proofs.GlobalsKernelComputation.compileDecs_function_eq, globalDeclarations_structural_eq]
theorem globalInitializers_structural_eq : globalInitializers = globalCompilationStructural.1 := by
  unfold globalInitializers globalCompilationStructural
  rw [InitECandidate.Proofs.GlobalsKernelComputation.compileDecs_function_eq, globalDeclarations_structural_eq]
#print axioms globalContext_structural_eq
#print axioms globalInitializers_structural_eq
end InitECandidate.Proofs.FrontendStages.Declarations
