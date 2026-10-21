import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify418
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData434 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "evm_empty" (Flapjack.Exp.const 0#64)
def simplifiedData434 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "evm_empty" (Flapjack.Exp.const 0#64)
def original434 := Pancake.PanLang.declToHOL originalData434
def simplified434 := Pancake.PanLang.declToHOL simplifiedData434
end InitECandidate.Proofs.FrontendStages.Declarations
