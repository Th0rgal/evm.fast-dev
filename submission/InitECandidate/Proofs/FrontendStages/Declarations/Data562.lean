import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify546
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData562 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "null_address" (Flapjack.Exp.const 0#64)
def simplifiedData562 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "null_address" (Flapjack.Exp.const 0#64)
def original562 := Pancake.PanLang.declToHOL originalData562
def simplified562 := Pancake.PanLang.declToHOL simplifiedData562
end InitECandidate.Proofs.FrontendStages.Declarations
