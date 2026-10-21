import InitECandidate.Proofs.FrontendStages.Declarations.Data1
import InitECandidate.Proofs.FrontendStages.Declarations.Data2
import InitECandidate.Proofs.FrontendStages.Declarations.Data5
import InitECandidate.Proofs.FrontendStages.Declarations.Data6
import InitECandidate.Proofs.FrontendStages.Declarations.Data38
import InitECandidate.Proofs.FrontendStages.Declarations.Data90
import InitECandidate.Proofs.FrontendStages.Declarations.Data91
import InitECandidate.Proofs.FrontendStages.Declarations.Data98
import InitECandidate.Proofs.FrontendStages.Declarations.Data99
import InitECandidate.Proofs.FrontendStages.Declarations.Data100
import InitECandidate.Proofs.FrontendStages.Declarations.Data148
import InitECandidate.Proofs.FrontendStages.Declarations.Data183
import InitECandidate.Proofs.FrontendStages.Declarations.Data184
import InitECandidate.Proofs.FrontendStages.Declarations.Data185
import InitECandidate.Proofs.FrontendStages.Declarations.Data234
import InitECandidate.Proofs.FrontendStages.Declarations.Data238
import InitECandidate.Proofs.FrontendStages.Declarations.Data239
import InitECandidate.Proofs.FrontendStages.Declarations.Data240
import InitECandidate.Proofs.FrontendStages.Declarations.Data241
import InitECandidate.Proofs.FrontendStages.Declarations.Data242
import InitECandidate.Proofs.FrontendStages.Declarations.Data345
import InitECandidate.Proofs.FrontendStages.Declarations.Data346
import InitECandidate.Proofs.FrontendStages.Declarations.Data347
import InitECandidate.Proofs.FrontendStages.Declarations.Data348
import InitECandidate.Proofs.FrontendStages.Declarations.Data349
import InitECandidate.Proofs.FrontendStages.Declarations.Data350
import InitECandidate.Proofs.FrontendStages.Declarations.Data400
import InitECandidate.Proofs.FrontendStages.Declarations.Data401
import InitECandidate.Proofs.FrontendStages.Declarations.Data402
import InitECandidate.Proofs.FrontendStages.Declarations.Data403
import InitECandidate.Proofs.FrontendStages.Declarations.Data404
import InitECandidate.Proofs.FrontendStages.Declarations.Data433
import InitECandidate.Proofs.FrontendStages.Declarations.Data434
import InitECandidate.Proofs.FrontendStages.Declarations.Data435
import InitECandidate.Proofs.FrontendStages.Declarations.Data436
import InitECandidate.Proofs.FrontendStages.Declarations.Data559
import InitECandidate.Proofs.FrontendStages.Declarations.Data560
import InitECandidate.Proofs.FrontendStages.Declarations.Data561
import InitECandidate.Proofs.FrontendStages.Declarations.Data562
import InitECandidate.Proofs.FrontendStages.Declarations.Data605
import InitECandidate.Proofs.FrontendStages.Declarations.Data606
import InitECandidate.Proofs.FrontendStages.Declarations.Data607
import InitECandidate.Proofs.FrontendStages.Declarations.Data608
import InitECandidate.Proofs.FrontendStages.Declarations.Data615
import InitECandidate.Proofs.FrontendStages.Declarations.Data616
import InitECandidate.Proofs.FrontendStages.Declarations.Data617
import InitECandidate.Proofs.FrontendStages.Declarations.Data643
import InitECandidate.Proofs.FrontendStages.Declarations.Data644
import InitECandidate.Proofs.FrontendStages.Declarations.Data692
import InitECandidate.Proofs.FrontendStages.Declarations.Data807
import InitECandidate.Proofs.FrontendStages.Declarations.Data842
import InitECandidate.Proofs.FrontendStages.Declarations.Data843
import InitECandidate.Proofs.FrontendStages.Declarations.Data844
import InitECandidate.Proofs.FrontendStages.Declarations.Data845
import InitECandidate.Proofs.FrontendStages.Declarations.Data846
import InitECandidate.Proofs.FrontendStages.Declarations.Data847
import InitECandidate.Proofs.FrontendStages.Declarations.Data848
import InitECandidate.Proofs.FrontendStages.Declarations.Data849
import InitECandidate.Proofs.FrontendStages.Declarations.Data850
import InitECandidate.Proofs.FrontendStages.Declarations.Data851
import InitECandidate.Proofs.FrontendStages.Declarations.Data852
import InitECandidate.Proofs.FrontendStages.Declarations.Data853
import InitECandidate.Proofs.FrontendStages.Declarations.Data854
import InitECandidate.Proofs.FrontendStages.Declarations.Data855
import InitECandidate.Proofs.FrontendStages.Declarations.Data856
import InitECandidate.Proofs.FrontendStages.Declarations.Data860
import InitECandidate.Proofs.FrontendStages.Declarations.Data885
import InitECandidate.Proofs.GlobalsComputation
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalDeclarations : List (Pancake.PanLang.DeclHOL 64) := [simplified1, simplified2, simplified5, simplified6, simplified38, simplified90, simplified91, simplified98, simplified99, simplified100, simplified148, simplified183, simplified184, simplified185, simplified234, simplified238, simplified239, simplified240, simplified241, simplified242, simplified345, simplified346, simplified347, simplified348, simplified349, simplified350, simplified400, simplified401, simplified402, simplified403, simplified404, simplified433, simplified434, simplified435, simplified436, simplified559, simplified560, simplified561, simplified562, simplified605, simplified606, simplified607, simplified608, simplified615, simplified616, simplified617, simplified643, simplified644, simplified692, simplified807, simplified842, simplified843, simplified844, simplified845, simplified846, simplified847, simplified848, simplified849, simplified850, simplified851, simplified852, simplified853, simplified854, simplified855, simplified856, simplified860, simplified885]
def globalInitial : PanGlobalsContextExact 64 :=
  { globals := HolFiniteMapExact.empty, globalsSize := 0,
    maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 67 }
def globalContext : PanGlobalsContextExact 64 :=
  (compileDecsExactHOL globalInitial globalDeclarations).2.2.2
def globalStart : Basis.Pure.MlString.MlString := Basis.Pure.MlString.ofString "main"
def globalNewStart : Basis.Pure.MlString.MlString := Flapjack.Basis.Pure.MlString.MlString.implode [109#8, 97#8, 105#8, 110#8, 39#8]
end InitECandidate.Proofs.FrontendStages.Declarations
