import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify387
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData403 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bal_idx_stor" (Flapjack.Exp.const 0#64)
def simplifiedData403 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bal_idx_stor" (Flapjack.Exp.const 0#64)
def original403 := Pancake.PanLang.declToHOL originalData403
def simplified403 := Pancake.PanLang.declToHOL simplifiedData403
end InitECandidate.Proofs.FrontendStages.Declarations
