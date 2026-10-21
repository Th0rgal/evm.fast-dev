import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify590
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData606 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "rmd_x" (Flapjack.Exp.const 0#64)
def simplifiedData606 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "rmd_x" (Flapjack.Exp.const 0#64)
def original606 := Pancake.PanLang.declToHOL originalData606
def simplified606 := Pancake.PanLang.declToHOL simplifiedData606
end InitECandidate.Proofs.FrontendStages.Declarations
