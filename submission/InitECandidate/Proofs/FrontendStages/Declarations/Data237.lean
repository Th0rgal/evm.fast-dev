import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify221
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData237 : Decl (BitVec 64) :=
Flapjack.Decl.exnDecl "MptErr" Flapjack.Shape.one
def simplifiedData237 : Decl (BitVec 64) :=
Flapjack.Decl.exnDecl "MptErr" Flapjack.Shape.one
def original237 := Pancake.PanLang.declToHOL originalData237
def simplified237 := Pancake.PanLang.declToHOL simplifiedData237
end InitECandidate.Proofs.FrontendStages.Declarations
