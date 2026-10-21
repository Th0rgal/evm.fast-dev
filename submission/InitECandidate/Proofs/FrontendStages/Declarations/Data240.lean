import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify224
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations

def originalData240 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "mpt_nib_scratch" (Flapjack.Exp.const 0#64)
def simplifiedData240 : Decl (BitVec 64) :=
Flapjack.Decl.decl Flapjack.Shape.one "mpt_nib_scratch" (Flapjack.Exp.const 0#64)
def original240 := Pancake.PanLang.declToHOL originalData240
def simplified240 := Pancake.PanLang.declToHOL simplifiedData240
end InitECandidate.Proofs.FrontendStages.Declarations
