import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify599
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData615 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "b2_sigma" (Flapjack.Exp.const 0#64)
def simplifiedData615 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "b2_sigma" (Flapjack.Exp.const 0#64)
def original615 := Pancake.PanLang.declToHOL originalData615
def simplified615 := Pancake.PanLang.declToHOL simplifiedData615
end InitECandidate.Proofs.FrontendStages.Declarations
