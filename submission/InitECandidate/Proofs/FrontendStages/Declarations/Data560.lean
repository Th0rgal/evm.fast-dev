import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify544
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData560 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "transfer_topic" (Flapjack.Exp.const 0#64)
def simplifiedData560 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "transfer_topic" (Flapjack.Exp.const 0#64)
def original560 := Pancake.PanLang.declToHOL originalData560
def simplified560 := Pancake.PanLang.declToHOL simplifiedData560
end InitECandidate.Proofs.FrontendStages.Declarations
