import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify331
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData347 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "ts" (Flapjack.Exp.const 0#64)
def simplifiedData347 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "ts" (Flapjack.Exp.const 0#64)
def original347 := Pancake.PanLang.declToHOL originalData347
def simplified347 := Pancake.PanLang.declToHOL simplifiedData347
end InitECandidate.Proofs.FrontendStages.Declarations
