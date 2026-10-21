import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify627
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData643 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bn_gamma" (Flapjack.Exp.const 0#64)
def simplifiedData643 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bn_gamma" (Flapjack.Exp.const 0#64)
def original643 := Pancake.PanLang.declToHOL originalData643
def simplified643 := Pancake.PanLang.declToHOL simplifiedData643
end InitECandidate.Proofs.FrontendStages.Declarations
