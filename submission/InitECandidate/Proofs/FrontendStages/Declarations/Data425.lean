import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify409
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body425_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "update_builder_from_tx" []

def body425_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merge_tx_into_block" []

def body425_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body425_3 : Prog (BitVec 64) :=
.seq body425_1 body425_2

def body425_4 : Prog (BitVec 64) :=
.seq body425_0 body425_3

def body425_5 : Prog (BitVec 64) :=
.seq body425_0 body425_1

def body425_6 : Prog (BitVec 64) :=
.seq body425_5 body425_2

def originalData425 : Decl (BitVec 64) :=
.function { name := "incorporate_tx_into_block", inline := false, exported := false, params := [], body := body425_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData425 : Decl (BitVec 64) :=
.function { name := "incorporate_tx_into_block", inline := false, exported := false, params := [], body := body425_6, returnShape := (Flapjack.Shape.one) }
def original425 := Pancake.PanLang.declToHOL originalData425
def simplified425 := Pancake.PanLang.declToHOL simplifiedData425
end InitECandidate.Proofs.FrontendStages.Declarations
