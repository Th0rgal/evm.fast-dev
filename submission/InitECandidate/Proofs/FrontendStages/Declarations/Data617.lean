import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify601
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData617 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "b2_v" (Flapjack.Exp.const 0#64)
def simplifiedData617 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "b2_v" (Flapjack.Exp.const 0#64)
def original617 := Pancake.PanLang.declToHOL originalData617
def simplified617 := Pancake.PanLang.declToHOL simplifiedData617
end InitECandidate.Proofs.FrontendStages.Declarations
