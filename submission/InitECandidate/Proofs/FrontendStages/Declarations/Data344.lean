import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify328
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData344 : Decl (BitVec 64) :=
Flapjack.Decl.exnDecl "StateErr" Flapjack.Shape.one
def simplifiedData344 : Decl (BitVec 64) :=
Flapjack.Decl.exnDecl "StateErr" Flapjack.Shape.one
def original344 := Pancake.PanLang.declToHOL originalData344
def simplified344 := Pancake.PanLang.declToHOL simplifiedData344
end InitECandidate.Proofs.FrontendStages.Declarations
