import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify310
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body326_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "tx_encode_generic"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]

def originalData326 : Decl (BitVec 64) :=
.function { name := "encode_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one)], body := body326_0, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData326 : Decl (BitVec 64) :=
.function { name := "encode_transaction", inline := false, exported := false, params := [("tx", Flapjack.Shape.one)], body := body326_0, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original326 := Pancake.PanLang.declToHOL originalData326
def simplified326 := Pancake.PanLang.declToHOL simplifiedData326
end InitECandidate.Proofs.FrontendStages.Declarations
