import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify592
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData608 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "rmd_pad" (Flapjack.Exp.const 0#64)
def simplifiedData608 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "rmd_pad" (Flapjack.Exp.const 0#64)
def original608 := Pancake.PanLang.declToHOL originalData608
def simplified608 := Pancake.PanLang.declToHOL simplifiedData608
end InitECandidate.Proofs.FrontendStages.Declarations
