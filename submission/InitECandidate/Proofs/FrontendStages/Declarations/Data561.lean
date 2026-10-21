import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify545
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData561 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "vm_system_address" (Flapjack.Exp.const 0#64)
def simplifiedData561 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "vm_system_address" (Flapjack.Exp.const 0#64)
def original561 := Pancake.PanLang.declToHOL originalData561
def simplified561 := Pancake.PanLang.declToHOL simplifiedData561
end InitECandidate.Proofs.FrontendStages.Declarations
