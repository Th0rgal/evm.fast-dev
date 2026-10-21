import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify543
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData559 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "cur_cont" (Flapjack.Exp.const 0#64)
def simplifiedData559 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "cur_cont" (Flapjack.Exp.const 0#64)
def original559 := Pancake.PanLang.declToHOL originalData559
def simplified559 := Pancake.PanLang.declToHOL simplifiedData559
end InitECandidate.Proofs.FrontendStages.Declarations
