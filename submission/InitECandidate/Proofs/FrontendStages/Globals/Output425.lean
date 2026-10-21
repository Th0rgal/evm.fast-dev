import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data425
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate409
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody425_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "update_builder_from_tx" []

def globalBody425_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merge_tx_into_block" []

def globalBody425_2 : Prog (BitVec 64) :=
.seq globalBody425_0 globalBody425_1

def globalBody425_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody425_4 : Prog (BitVec 64) :=
.seq globalBody425_2 globalBody425_3

def globalData425 : Decl (BitVec 64) :=
.function { name := "incorporate_tx_into_block", inline := false, exported := false, params := [], body := globalBody425_4, returnShape := (Flapjack.Shape.one) }
def globalOutput425 := Pancake.PanLang.declToHOL globalData425
end InitECandidate.Proofs.FrontendStages.Declarations
