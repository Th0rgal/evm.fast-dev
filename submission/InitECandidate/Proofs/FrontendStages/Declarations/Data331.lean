import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify315
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body331_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "tx_signing_hash_mode"
  [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def originalData331 : Decl (BitVec 64) :=
.function { name := "signing_hash_2930", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body331_0, returnShape := (Flapjack.Shape.one) }
def simplifiedData331 : Decl (BitVec 64) :=
.function { name := "signing_hash_2930", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body331_0, returnShape := (Flapjack.Shape.one) }
def original331 := Pancake.PanLang.declToHOL originalData331
def simplified331 := Pancake.PanLang.declToHOL simplifiedData331
end InitECandidate.Proofs.FrontendStages.Declarations
