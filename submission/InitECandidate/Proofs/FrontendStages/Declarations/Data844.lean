import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify828
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData844 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "precompile_addrs" (Flapjack.Exp.const 0#64)
def simplifiedData844 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "precompile_addrs" (Flapjack.Exp.const 0#64)
def original844 := Pancake.PanLang.declToHOL originalData844
def simplified844 := Pancake.PanLang.declToHOL simplifiedData844
end InitECandidate.Proofs.FrontendStages.Declarations
