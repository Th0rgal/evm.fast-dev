import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify214
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body230_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r")

def body230_1 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("taylor_exponential") ([Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "excess_blob_gas", Flapjack.Exp.const 11684671#64]) body230_0

def originalData230 : Decl (BitVec 64) :=
.function { name := "calculate_blob_gas_price", inline := false, exported := false, params := [("excess_blob_gas", Flapjack.Shape.one)], body := body230_1, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData230 : Decl (BitVec 64) :=
.function { name := "calculate_blob_gas_price", inline := false, exported := false, params := [("excess_blob_gas", Flapjack.Shape.one)], body := body230_1, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original230 := Pancake.PanLang.declToHOL originalData230
def simplified230 := Pancake.PanLang.declToHOL simplifiedData230
end InitECandidate.Proofs.FrontendStages.Declarations
