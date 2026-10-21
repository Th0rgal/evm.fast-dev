import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify825
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData841 : Decl (BitVec 64) :=
Flapjack.Decl.exnDecl "Fail" Flapjack.Shape.one
def simplifiedData841 : Decl (BitVec 64) :=
Flapjack.Decl.exnDecl "Fail" Flapjack.Shape.one
def original841 := Pancake.PanLang.declToHOL originalData841
def simplified841 := Pancake.PanLang.declToHOL simplifiedData841
end InitECandidate.Proofs.FrontendStages.Declarations
