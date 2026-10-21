import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify417
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData433 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "ev" (Flapjack.Exp.const 0#64)
def simplifiedData433 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "ev" (Flapjack.Exp.const 0#64)
def original433 := Pancake.PanLang.declToHOL originalData433
def simplified433 := Pancake.PanLang.declToHOL simplifiedData433
end InitECandidate.Proofs.FrontendStages.Declarations
