import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify386
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData402 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bal_idx_accts" (Flapjack.Exp.const 0#64)
def simplifiedData402 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bal_idx_accts" (Flapjack.Exp.const 0#64)
def original402 := Pancake.PanLang.declToHOL originalData402
def simplified402 := Pancake.PanLang.declToHOL simplifiedData402
end InitECandidate.Proofs.FrontendStages.Declarations
