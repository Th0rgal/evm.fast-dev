import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify416
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData432 : Decl (BitVec 64) :=
Flapjack.Decl.exnDecl "EvmErr" Flapjack.Shape.one
def simplifiedData432 : Decl (BitVec 64) :=
Flapjack.Decl.exnDecl "EvmErr" Flapjack.Shape.one
def original432 := Pancake.PanLang.declToHOL originalData432
def simplified432 := Pancake.PanLang.declToHOL simplifiedData432
end InitECandidate.Proofs.FrontendStages.Declarations
