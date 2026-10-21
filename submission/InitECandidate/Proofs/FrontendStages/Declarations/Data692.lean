import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify676
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData692 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bls_c" (Flapjack.Exp.const 0#64)
def simplifiedData692 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bls_c" (Flapjack.Exp.const 0#64)
def original692 := Pancake.PanLang.declToHOL originalData692
def simplified692 := Pancake.PanLang.declToHOL simplifiedData692
end InitECandidate.Proofs.FrontendStages.Declarations
