import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify384
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData400 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bal_accounts" (Flapjack.Exp.const 0#64)
def simplifiedData400 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bal_accounts" (Flapjack.Exp.const 0#64)
def original400 := Pancake.PanLang.declToHOL originalData400
def simplified400 := Pancake.PanLang.declToHOL simplifiedData400
end InitECandidate.Proofs.FrontendStages.Declarations
