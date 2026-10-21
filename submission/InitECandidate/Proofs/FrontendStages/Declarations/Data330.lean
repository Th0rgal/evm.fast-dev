import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify314
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body330_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "tx_signing_hash_mode"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 2#64,
    Flapjack.Exp.var Flapjack.VarKind.local "chain_id", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def originalData330 : Decl (BitVec 64) :=
.function { name := "signing_hash_155", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body330_0, returnShape := (Flapjack.Shape.one) }
def simplifiedData330 : Decl (BitVec 64) :=
.function { name := "signing_hash_155", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("chain_id", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body330_0, returnShape := (Flapjack.Shape.one) }
def original330 := Pancake.PanLang.declToHOL originalData330
def simplified330 := Pancake.PanLang.declToHOL simplifiedData330
end InitECandidate.Proofs.FrontendStages.Declarations
