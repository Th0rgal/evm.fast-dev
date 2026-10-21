import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify826
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData842 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "be" (Flapjack.Exp.const 0#64)
def simplifiedData842 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "be" (Flapjack.Exp.const 0#64)
def original842 := Pancake.PanLang.declToHOL originalData842
def simplified842 := Pancake.PanLang.declToHOL simplifiedData842
end InitECandidate.Proofs.FrontendStages.Declarations
