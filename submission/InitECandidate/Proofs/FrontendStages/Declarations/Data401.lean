import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify385
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData401 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bal_index" (Flapjack.Exp.const 0#64)
def simplifiedData401 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bal_index" (Flapjack.Exp.const 0#64)
def original401 := Pancake.PanLang.declToHOL originalData401
def simplified401 := Pancake.PanLang.declToHOL simplifiedData401
end InitECandidate.Proofs.FrontendStages.Declarations
