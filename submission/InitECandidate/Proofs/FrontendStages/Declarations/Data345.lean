import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify329
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData345 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "ws" (Flapjack.Exp.const 0#64)
def simplifiedData345 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "ws" (Flapjack.Exp.const 0#64)
def original345 := Pancake.PanLang.declToHOL originalData345
def simplified345 := Pancake.PanLang.declToHOL simplifiedData345
end InitECandidate.Proofs.FrontendStages.Declarations
