import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify628
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData644 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bn_expw" (Flapjack.Exp.const 0#64)
def simplifiedData644 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bn_expw" (Flapjack.Exp.const 0#64)
def original644 := Pancake.PanLang.declToHOL originalData644
def simplified644 := Pancake.PanLang.declToHOL simplifiedData644
end InitECandidate.Proofs.FrontendStages.Declarations
