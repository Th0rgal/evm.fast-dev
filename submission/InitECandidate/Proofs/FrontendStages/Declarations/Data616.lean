import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify600
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData616 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "b2_iv" (Flapjack.Exp.const 0#64)
def simplifiedData616 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "b2_iv" (Flapjack.Exp.const 0#64)
def original616 := Pancake.PanLang.declToHOL originalData616
def simplified616 := Pancake.PanLang.declToHOL simplifiedData616
end InitECandidate.Proofs.FrontendStages.Declarations
