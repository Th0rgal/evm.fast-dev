import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify791
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData807 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bls_discount" (Flapjack.Exp.const 0#64)
def simplifiedData807 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "bls_discount" (Flapjack.Exp.const 0#64)
def original807 := Pancake.PanLang.declToHOL originalData807
def simplified807 := Pancake.PanLang.declToHOL simplifiedData807
end InitECandidate.Proofs.FrontendStages.Declarations
