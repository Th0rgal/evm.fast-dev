import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data798
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate782
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody798_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_consts_init" []

def globalBody798_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody798_2 : Prog (BitVec 64) :=
.seq globalBody798_0 globalBody798_1

def globalData798 : Decl (BitVec 64) :=
.function { name := "bls_lib_init", inline := false, exported := false, params := [], body := globalBody798_2, returnShape := (Flapjack.Shape.one) }
def globalOutput798 := Pancake.PanLang.declToHOL globalData798
end InitECandidate.Proofs.FrontendStages.Declarations
